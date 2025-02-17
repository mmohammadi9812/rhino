use builtins::builtins;
use graph::{strongly_connected_components, Graph, VertexIndex};
use interner::*;
use lexer::Location;
use module::Expr::*;
use module::LiteralData::*;
use module::*;
use renamer::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::error;
use std::fmt;
use std::mem::swap;

pub type TcType = Type<Name>;

///Trait which can be implemented by types where types can be looked up by name
pub trait Types {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<TcType, Name>>;
    fn find_class<'a>(
        &'a self,
        name: Name,
    ) -> Option<(
        &'a [Constraint<Name>],
        &'a TypeVariable,
        &'a [TypeDeclaration<Name>],
    )>;
    fn has_instance(&self, classname: Name, typ: &TcType) -> bool {
        match self.find_instance(classname, typ) {
            Some(_) => true,
            None => false,
        }
    }
    fn find_instance<'a>(
        &'a self,
        classname: Name,
        typ: &TcType,
    ) -> Option<(&'a [Constraint<Name>], &'a TcType)>;
}

///A trait which also allows for lookup of data types
pub trait DataTypes: Types {
    fn find_data_type<'a>(&'a self, name: Name) -> Option<&'a DataDefinition<Name>>;
}

impl Types for Module<Name> {
    fn find_type<'a>(&'a self, name: &Name) -> Option<&'a Qualified<TcType, Name>> {
        for bind in self.bindings.iter() {
            if bind.name == *name {
                return Some(&bind.typ);
            }
        }

        for class in self.classes.iter() {
            for decl in class.declarations.iter() {
                if *name == decl.name {
                    return Some(&decl.typ);
                }
            }
        }
        for data in self.data_definitions.iter() {
            for ctor in data.constructors.iter() {
                if *name == ctor.name {
                    return Some(&ctor.typ);
                }
            }
        }
        self.newtypes
            .iter()
            .find(|newtype| newtype.constructor_name == *name)
            .map(|newtype| &newtype.constructor_type)
    }

    fn find_class<'a>(
        &'a self,
        name: Name,
    ) -> Option<(
        &'a [Constraint<Name>],
        &'a TypeVariable,
        &'a [TypeDeclaration<Name>],
    )> {
        self.classes
            .iter()
            .find(|class| name == class.name)
            .map(|class| {
                (
                    class.constraints.as_ref(),
                    &class.variable,
                    class.declarations.as_ref(),
                )
            })
    }

    fn find_instance<'a>(
        &'a self,
        classname: Name,
        typ: &TcType,
    ) -> Option<(&'a [Constraint<Name>], &'a TcType)> {
        for instance in self.instances.iter() {
            if classname == instance.classname
                && extract_applied_type(&instance.typ) == extract_applied_type(typ)
            {
                //test name
                return Some((instance.constraints.as_ref(), &instance.typ));
            }
        }
        None
    }
}

impl DataTypes for Module<Name> {
    fn find_data_type<'a>(&'a self, name: Name) -> Option<&'a DataDefinition<Name>> {
        for data in self.data_definitions.iter() {
            if name == extract_applied_type(&data.typ.value).ctor().name {
                return Some(data);
            }
        }
        None
    }
}

///The TypeEnvironment stores most data which is needed as typechecking is performed.
pub struct TypeEnvironment<'a> {
    ///Stores references to imported modules or assemblies
    assemblies: Vec<&'a (dyn DataTypes + 'a)>,
    ///A mapping of names to the type which those names are bound to.
    named_types: HashMap<Name, Qualified<TcType, Name>>,
    ///A mapping used for any variables declared inside any global binding.
    ///Used in conjuction to the global 'named_types' map since the local table can
    ///be cleared once those bindings are no longer in used which gives an overall speed up.
    local_types: HashMap<Name, Qualified<TcType, Name>>,
    ///Stores the constraints for each typevariable since the typevariables cannot themselves store this.
    constraints: HashMap<TypeVariable, Vec<Name>>,
    ///Stores data about the instances which are available.
    ///1: Any constraints for the type which the instance is for
    ///2: The name of the class
    ///3: The Type which the instance is defined for
    instances: Vec<(Vec<Constraint<Name>>, Name, TcType)>,
    classes: Vec<(Vec<Constraint<Name>>, Name)>,
    data_definitions: Vec<DataDefinition<Name>>,
    ///The current age for newly created variables.
    ///Age is used to determine whether variables need to be quantified or not.
    variable_age: isize,
    errors: Errors<TypeErrorInfo>,
}

#[derive(Debug)]
pub struct TypeError(Errors<TypeErrorInfo>);

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.report_errors(f, "typecheck")
    }
}

impl error::Error for TypeError {
    fn description(&self) -> &str {
        "type error"
    }
}

///A Substitution is a mapping from typevariables to types.
#[derive(Clone)]
pub struct Substitution {
    ///A hashmap which contains what a typevariable is unified to.
    subs: HashMap<TypeVariable, TcType>,
}

///Trait which provides access to the bindings in a struct.
pub trait Bindings {
    fn get_mut(&mut self, idx: (usize, usize)) -> &mut [Binding<Name>];

    fn each_binding(&self, func: &mut dyn FnMut(&[Binding<Name>], (usize, usize)));
}

impl Bindings for Module<Name> {
    fn get_mut(&mut self, (instance_idx, idx): (usize, usize)) -> &mut [Binding<Name>] {
        let bindings = if instance_idx == 0 {
            &mut *self.bindings
        } else if instance_idx - 1 < self.instances.len() {
            &mut *self.instances[instance_idx - 1].bindings
        } else {
            &mut *self.classes[instance_idx - 1 - self.instances.len()].bindings
        };
        mut_bindings_at(bindings, idx)
    }

    fn each_binding(&self, func: &mut dyn FnMut(&[Binding<Name>], (usize, usize))) {
        let mut index = 0;
        for binds in binding_groups(self.bindings.as_ref()) {
            func(binds, (0, index));
            index += binds.len();
        }
        for (instance_index, instance) in self.instances.iter().enumerate() {
            index = 0;
            for binds in binding_groups(instance.bindings.as_ref()) {
                func(binds, (instance_index + 1, index));
                index += binds.len();
            }
        }
        for (class_index, class) in self.classes.iter().enumerate() {
            index = 0;
            for binds in binding_groups(class.bindings.as_ref()) {
                func(binds, (class_index + 1 + self.instances.len(), index));
                index += binds.len();
            }
        }
    }
}

fn mut_bindings_at<'a, Ident: Eq>(
    bindings: &'a mut [Binding<Ident>],
    idx: usize,
) -> &'a mut [Binding<Ident>] {
    let end = bindings[idx..]
        .iter()
        .position(|bind| bind.name != bindings[idx].name)
        .unwrap_or(bindings.len() - idx);
    &mut bindings[idx..idx + end]
}

//Woraround since traits around a vector seems problematic
struct BindingsWrapper<'a> {
    value: &'a mut [Binding<Name>],
}

impl<'a> Bindings for BindingsWrapper<'a> {
    fn get_mut(&mut self, (_, idx): (usize, usize)) -> &mut [Binding<Name>] {
        mut_bindings_at(self.value, idx)
    }

    fn each_binding(&self, func: &mut dyn FnMut(&[Binding<Name>], (usize, usize))) {
        let mut index = 0;
        for binds in binding_groups(self.value.as_ref()) {
            func(binds, (0, index));
            index += binds.len();
        }
    }
}

fn insert_to(map: &mut HashMap<Name, Qualified<TcType, Name>>, name: &str, typ: TcType) {
    map.insert(
        Name {
            name: intern(name),
            uid: 0,
        },
        qualified(vec![], typ),
    );
}
fn prim(typename: &str, op: &str) -> ::std::string::String {
    let mut b = "prim".to_string();
    b.push_str(typename);
    b.push_str(op);
    b
}
fn add_primitives(globals: &mut HashMap<Name, Qualified<TcType, Name>>, typename: &str) {
    let typ = Type::new_op(name(typename), vec![]);
    {
        let binop = typ::function_type(&typ, &typ::function_type(&typ, &typ));
        insert_to(globals, prim(typename, "Add").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "Subtract").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "Multiply").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "Divide").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "Remainder").as_ref(), binop.clone());
    }
    {
        let binop = typ::function_type_(typ.clone(), typ::function_type_(typ, typ::bool_type()));
        insert_to(globals, prim(typename, "EQ").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "LT").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "LE").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "GT").as_ref(), binop.clone());
        insert_to(globals, prim(typename, "GE").as_ref(), binop.clone());
    }
}

impl<'a> TypeEnvironment<'a> {
    ///Creates a new TypeEnvironment and adds all the primitive types
    pub fn new() -> TypeEnvironment<'a> {
        let mut globals = HashMap::new();
        add_primitives(&mut globals, "Int");
        add_primitives(&mut globals, "Double");
        insert_to(
            &mut globals,
            "primIntToDouble",
            typ::function_type_(typ::int_type(), typ::double_type()),
        );
        insert_to(
            &mut globals,
            "primDoubleToInt",
            typ::function_type_(typ::double_type(), typ::int_type()),
        );
        let var = Type::Generic(TypeVariable::new_var_kind(intern("a"), Kind::Star.clone()));

        for (name, typ) in builtins().into_iter() {
            insert_to(&mut globals, name, typ);
        }
        let list = typ::list_type(var.clone());
        insert_to(&mut globals, "[]", list.clone());
        insert_to(
            &mut globals,
            ":",
            typ::function_type(&var, &typ::function_type(&list, &list)),
        );
        insert_to(&mut globals, "()", typ::unit());
        for i in (2 as usize)..10 {
            let (name, typ) = typ::tuple_type(i);
            insert_to(&mut globals, name.as_ref(), typ);
        }
        TypeEnvironment {
            assemblies: Vec::new(),
            named_types: globals,
            local_types: HashMap::new(),
            constraints: HashMap::new(),
            instances: Vec::new(),
            classes: Vec::new(),
            data_definitions: Vec::new(),
            variable_age: 0,
            errors: Errors::new(),
        }
    }

    pub fn add_types(&mut self, types: &'a dyn DataTypes) {
        self.assemblies.push(types);
    }

    ///Typechecks a module
    ///If the typecheck is successful the types in the module are updated with the new types.
    ///If any errors were found while typechecking panic! is called.
    pub fn typecheck_module(&mut self, module: &mut Module<Name>) -> Result<(), TypeError> {
        self.typecheck_module2(module);
        self.errors.into_result(()).map_err(TypeError)
    }
    pub fn typecheck_module2(&mut self, module: &mut Module<Name>) {
        let start_var_age = self.variable_age + 1;
        for data_def in module.data_definitions.iter_mut() {
            for constructor in data_def.constructors.iter_mut() {
                let mut typ = constructor.typ.clone();
                quantify(0, &mut typ);
                self.named_types.insert(constructor.name.clone(), typ);
            }
            self.data_definitions.push(data_def.clone());
        }
        for newtype in module.newtypes.iter() {
            let mut typ = newtype.constructor_type.clone();
            quantify(0, &mut typ);
            self.named_types
                .insert(newtype.constructor_name.clone(), typ);
        }
        for class in module.classes.iter_mut() {
            //Instantiate a new variable and replace all occurances of the class variable with this
            let mut var_kind = None;
            for type_decl in class.declarations.iter_mut() {
                var_kind = match find_kind(&class.variable, var_kind, &type_decl.typ.value) {
                    Ok(k) => k,
                    Err(msg) => panic!("{:?}", msg),
                };
                //If we found the variable, update it immediatly since the kind of th variable
                //matters when looking for constraints, etc
                match var_kind {
                    Some(ref k) => {
                        class.variable.kind.clone_from(k);
                    }
                    None => (),
                }

                let c = Constraint {
                    class: class.name.clone(),
                    variables: vec![class.variable.clone()],
                };
                {
                    //Workaround to add the class's constraints directyly to the declaration
                    let mut context = vec![];
                    swap(&mut context, &mut type_decl.typ.constraints);
                    let mut vec_context: Vec<Constraint<Name>> = context.into_iter().collect();
                    vec_context.push(c);
                    type_decl.typ.constraints = vec_context;
                }
                let mut t = type_decl.typ.clone();
                quantify(0, &mut t);
                self.named_types.insert(type_decl.name.clone(), t);
            }
            for binding in class.bindings.iter_mut() {
                let classname = &class.name;
                let decl = class
                    .declarations
                    .iter()
                    .find(|decl| binding.name.name.as_ref().ends_with(decl.name.as_ref()))
                    .unwrap_or_else(|| {
                        panic!("Could not find {:?} in class {:?}", binding.name, classname)
                    });
                binding.typ = decl.typ.clone();
                {
                    let mut context = vec![];
                    swap(&mut context, &mut binding.typ.constraints);
                    let mut vec_context: Vec<Constraint<Name>> = context.into_iter().collect();
                    let c = Constraint {
                        class: class.name.clone(),
                        variables: vec![class.variable.clone()],
                    };
                    vec_context.push(c);
                    binding.typ.constraints = vec_context;
                }
            }
            self.classes
                .push((class.constraints.clone(), class.name.clone()));
        }
        let data_definitions = module.data_definitions.clone();
        for instance in module.instances.iter_mut() {
            let (_class_constraints, class_var, class_decls) = module
                .classes
                .iter()
                .find(|class| class.name == instance.classname)
                .map(|class| {
                    (
                        class.constraints.as_ref(),
                        &class.variable,
                        class.declarations.as_ref(),
                    )
                })
                .or_else(|| {
                    self.assemblies
                        .iter()
                        .filter_map(|a| a.find_class(instance.classname))
                        .next()
                })
                .unwrap_or_else(|| panic!("Could not find class {:?}", instance.classname));
            //Update the kind of the type for the instance to be the same as the class kind (since we have no proper kind inference
            match instance.typ {
                Type::Constructor(ref mut op) => {
                    let maybe_data = self
                        .assemblies
                        .iter()
                        .filter_map(|a| a.find_data_type(op.name))
                        .next();
                    op.kind = maybe_data
                        .or_else(|| {
                            data_definitions.iter().find(|data| {
                                op.name == extract_applied_type(&data.typ.value).ctor().name
                            })
                        })
                        .map(|data| extract_applied_type(&data.typ.value).kind().clone())
                        .unwrap_or_else(|| {
                            if intern("[]") == op.name {
                                Kind::Function(box Kind::Star, box Kind::Star)
                            } else {
                                Kind::Star
                            }
                        });
                }
                _ => (),
            }
            for binding in instance.bindings.iter_mut() {
                let classname = &instance.classname;
                let decl = class_decls
                    .iter()
                    .find(|decl| binding.name.as_ref().ends_with(decl.name.as_ref()))
                    .unwrap_or_else(|| {
                        panic!("Could not find {:?} in class {:?}", binding.name, classname)
                    });
                binding.typ = decl.typ.clone();
                replace_var(&mut binding.typ.value, class_var, &instance.typ);
                self.freshen_qualified_type(&mut binding.typ, HashMap::new());
                {
                    let mut context = vec![];
                    swap(&mut context, &mut binding.typ.constraints);
                    let mut vec_context: Vec<Constraint<Name>> = context.into_iter().collect();
                    for constraint in instance.constraints.iter() {
                        vec_context.push(constraint.clone());
                    }
                    binding.typ.constraints = vec_context;
                }
            }
            {
                let mut missing_super_classes = self
                    .find_class_constraints(instance.classname)
                    .unwrap_or_else(|| panic!("Error: Missing class {:?}", instance.classname))
                    .iter() //Make sure we have an instance for all of the constraints
                    .filter(|constraint| {
                        self.has_instance(constraint.class, &instance.typ, &mut Vec::new())
                            .is_err()
                    })
                    .peekable();
                if missing_super_classes.peek().is_some() {
                    let mut buffer = ::std::string::String::new();
                    buffer.push_str(missing_super_classes.next().unwrap().class.as_ref());
                    for constraint in missing_super_classes {
                        buffer.push_str(", ");
                        buffer.push_str(constraint.class.as_ref());
                    }
                    panic!("The type {:?} does not have all necessary super class instances required for {:?}.\n Missing: {:?}",
                        instance.typ, instance.classname, buffer);
                }
            }
            self.instances.push((
                instance.constraints.clone(),
                instance.classname.clone(),
                instance.typ.clone(),
            ));
        }

        for type_decl in module.type_declarations.iter_mut() {
            match module
                .bindings
                .iter_mut()
                .find(|bind| bind.name == type_decl.name)
            {
                Some(bind) => {
                    bind.typ = type_decl.typ.clone();
                }
                None => panic!(
                    "Error: Type declaration for '{:?}' has no binding",
                    type_decl.name
                ),
            }
        }

        {
            let mut subs = Substitution {
                subs: HashMap::new(),
            };
            self.typecheck_global_bindings(start_var_age, &mut subs, module);
        }
    }

    ///Typechecks an expression.
    ///The types in the expression are updated with the correct types.
    ///If the expression has a type error, fail is called.
    pub fn typecheck_expr(&mut self, expr: &mut TypedExpr<Name>) -> Result<(), TypeError> {
        let mut subs = Substitution {
            subs: HashMap::new(),
        };
        let mut typ = self.typecheck(expr, &mut subs);
        unify_location(self, &mut subs, &expr.location, &mut typ, &mut expr.typ);
        self.substitute(&mut subs, expr);
        self.errors.into_result(()).map_err(TypeError)
    }

    pub fn typecheck_module_(&mut self, module: &mut Module<Name>) {
        self.typecheck_module(module).unwrap()
    }
    pub fn typecheck_expr_(&mut self, expr: &mut TypedExpr<Name>) {
        self.typecheck_expr(expr).unwrap()
    }

    ///Finds all the constraints for a type
    pub fn find_constraints(&self, typ: &TcType) -> Vec<Constraint<Name>> {
        let mut result: Vec<Constraint<Name>> = Vec::new();
        each_type(
            typ,
            |var| match self.constraints.get(var) {
                Some(constraints) => {
                    for c in constraints.iter() {
                        if result
                            .iter()
                            .find(|x| x.class == *c && x.variables[0] == *var)
                            == None
                        {
                            result.push(Constraint {
                                class: c.clone(),
                                variables: vec![var.clone()],
                            });
                        }
                    }
                }
                None => (),
            },
            |_| (),
        );
        result
    }
    fn find_data_definition(&self, name: Name) -> Option<&DataDefinition<Name>> {
        self.data_definitions
            .iter()
            .find(|data| extract_applied_type(&data.typ.value).ctor().name == name)
            .or_else(|| {
                self.assemblies
                    .iter()
                    .filter_map(|a| a.find_data_type(name))
                    .next()
            })
    }

    fn freshen_qualified_type(
        &mut self,
        typ: &mut Qualified<TcType, Name>,
        mut mapping: HashMap<TypeVariable, TcType>,
    ) {
        for constraint in typ.constraints.iter_mut() {
            let old = constraint.variables[0].clone();
            let new = match mapping.entry(old.clone()) {
                Entry::Vacant(entry) => entry.insert(self.new_var_kind(old.kind.clone())),
                Entry::Occupied(entry) => entry.into_mut(),
            };
            constraint.variables[0] = new.var().clone();
        }
        let mut subs = Substitution { subs: mapping };
        freshen_all(self, &mut subs, &mut typ.value);
    }
    fn apply_locals(&mut self, subs: &Substitution) {
        for (_, typ) in self.local_types.iter_mut() {
            replace(&mut self.constraints, &mut typ.value, subs);
        }
    }

    ///Walks through an expression and applies the substitution on each of its types
    fn substitute(&mut self, subs: &Substitution, expr: &mut TypedExpr<Name>) {
        struct SubVisitor<'a: 'b, 'b, 'c> {
            env: &'b mut TypeEnvironment<'a>,
            subs: &'c Substitution,
        }
        impl<'a, 'b, 'c> MutVisitor<Name> for SubVisitor<'a, 'b, 'c> {
            fn visit_expr(&mut self, expr: &mut TypedExpr<Name>) {
                replace(&mut self.env.constraints, &mut expr.typ, self.subs);
                walk_expr_mut(self, expr);
            }
        }
        SubVisitor {
            env: self,
            subs: subs,
        }
        .visit_expr(expr);
    }

    ///Returns whether the type 'searched_type' has an instance for 'class'
    ///If no instance was found, return the instance which was missing
    fn has_instance(
        &self,
        class: Name,
        searched_type: &TcType,
        new_constraints: &mut Vec<Constraint<Name>>,
    ) -> Result<(), InternedStr> {
        match extract_applied_type(searched_type) {
            &Type::Constructor(ref ctor) => match self.find_data_definition(ctor.name) {
                Some(data_type) => {
                    if data_type.deriving.iter().any(|name| *name == class) {
                        return self.check_instance_constraints(
                            &[],
                            &data_type.typ.value,
                            searched_type,
                            new_constraints,
                        );
                    }
                }
                None => (),
            },
            _ => (),
        }
        for &(ref constraints, ref name, ref typ) in self.instances.iter() {
            if class == *name {
                let result = self.check_instance_constraints(
                    &**constraints,
                    typ,
                    searched_type,
                    new_constraints,
                );
                if result.is_ok() {
                    return result;
                }
            }
        }

        for types in self.assemblies.iter() {
            match types.find_instance(class, searched_type) {
                Some((constraints, unspecialized_type)) => {
                    return self.check_instance_constraints(
                        constraints,
                        unspecialized_type,
                        searched_type,
                        new_constraints,
                    );
                }
                None => (),
            }
        }
        Err(class.name)
    }

    fn find_class_constraints(&self, class: Name) -> Option<&[Constraint<Name>]> {
        self.classes
            .iter()
            .find(|&&(_, ref name)| *name == class)
            .map(|x| x.0.as_ref())
            .or_else(|| {
                self.assemblies
                    .iter()
                    .filter_map(|types| types.find_class(class)) //Find the class
                    .next() //next will get us the first class (but should only be one)
                    .map(|(constraints, _, _)| constraints)
            })
    }

    ///Checks whether 'actual_type' fulfills all the constraints that the instance has.
    fn check_instance_constraints(
        &self,
        constraints: &[Constraint<Name>],
        instance_type: &TcType,
        actual_type: &TcType,
        new_constraints: &mut Vec<Constraint<Name>>,
    ) -> Result<(), InternedStr> {
        match (instance_type, actual_type) {
            (&Type::Application(ref lvar, ref r), &Type::Application(ref ltype, ref rtype)) => {
                if let Type::Variable(ref rvar) = **r {
                    constraints
                        .iter()
                        .filter(|c| c.variables[0] == *rvar)
                        .map(|constraint| {
                            let result =
                                self.has_instance(constraint.class, &**rtype, new_constraints);
                            if result.is_ok() {
                                match **rtype {
                                    Type::Variable(ref var) => {
                                        new_constraints.push(Constraint {
                                            class: constraint.class,
                                            variables: vec![var.clone()],
                                        });
                                    }
                                    _ => (),
                                }
                            }
                            result
                        })
                        .find(|result| result.is_err())
                        .unwrap_or_else(|| {
                            self.check_instance_constraints(
                                constraints,
                                &**lvar,
                                &**ltype,
                                new_constraints,
                            )
                        })
                } else {
                    Err(intern("Unknown error"))
                }
            }
            (&Type::Constructor(ref l), &Type::Constructor(ref r)) if l.name == r.name => Ok(()),
            (_, &Type::Variable(_)) => Ok(()),
            _ => Err(intern("Unknown error")),
        }
    }
    ///Creates a new type variable with a kind
    fn new_var_kind(&mut self, kind: Kind) -> TcType {
        self.variable_age += 1;
        let mut var = Type::new_var_kind(intern(self.variable_age.to_string().as_ref()), kind);
        match var {
            Type::Variable(ref mut var) => var.age = self.variable_age,
            _ => (),
        }
        var
    }

    ///Creates a new type variable with the kind Kind::Star
    fn new_var(&mut self) -> TcType {
        self.new_var_kind(Kind::Star)
    }

    ///Typechecks a Match
    fn typecheck_match(&mut self, matches: &mut Match<Name>, subs: &mut Substitution) -> TcType {
        match *matches {
            Match::Simple(ref mut e) => {
                let mut typ = self.typecheck(e, subs);
                unify_location(self, subs, &e.location, &mut typ, &mut e.typ);
                typ
            }
            Match::Guards(ref mut gs) => {
                let mut typ = None;
                for guard in gs.iter_mut() {
                    let mut typ2 = self.typecheck(&mut guard.expression, subs);
                    unify_location(
                        self,
                        subs,
                        &guard.expression.location,
                        &mut typ2,
                        &mut guard.expression.typ,
                    );
                    match typ {
                        Some(mut typ) => unify_location(
                            self,
                            subs,
                            &guard.expression.location,
                            &mut typ,
                            &mut typ2,
                        ),
                        None => (),
                    }
                    typ = Some(typ2);
                    let mut predicate = self.typecheck(&mut guard.predicate, subs);
                    unify_location(
                        self,
                        subs,
                        &guard.predicate.location,
                        &mut predicate,
                        &mut typ::bool_type(),
                    );
                    unify_location(
                        self,
                        subs,
                        &guard.predicate.location,
                        &mut predicate,
                        &mut guard.predicate.typ,
                    );
                }
                typ.unwrap()
            }
        }
    }

    ///Typechecks an expression
    fn typecheck(&mut self, expr: &mut TypedExpr<Name>, subs: &mut Substitution) -> TcType {
        if expr.typ == Type::<Name>::new_var(intern("a")) {
            expr.typ = self.new_var();
        }

        let x = match expr.expr {
            Literal(ref lit) => {
                match *lit {
                    Integral(_) => {
                        self.constraints
                            .insert(expr.typ.var().clone(), vec![prelude_name("Num")]);
                        match expr.typ {
                            Type::Variable(ref mut v) => v.kind = Kind::Star.clone(),
                            _ => (),
                        }
                    }
                    Fractional(_) => {
                        self.constraints
                            .insert(expr.typ.var().clone(), vec![prelude_name("Fractional")]);
                        match expr.typ {
                            Type::Variable(ref mut v) => v.kind = Kind::Star.clone(),
                            _ => (),
                        }
                    }
                    String(_) => {
                        expr.typ = typ::list_type(typ::char_type());
                    }
                    Char(_) => {
                        expr.typ = typ::char_type();
                    }
                }
                expr.typ.clone()
            }
            Identifier(ref name) => match self.fresh(name) {
                Some(t) => {
                    tracing::debug!("{:?} as {:?}", &name, &t);
                    expr.typ = t.clone();
                    t
                }
                None => panic!("Undefined identifier '{:?}' at {:?}", *name, expr.location),
            },
            Apply(ref mut func, ref mut arg) => {
                let func_type = self.typecheck(&mut **func, subs);
                self.typecheck_apply(&expr.location, subs, func_type, &mut **arg)
            }
            OpApply(ref mut lhs, ref op, ref mut rhs) => {
                let op_type = match self.fresh(op) {
                    Some(typ) => typ,
                    None => panic!("Undefined identifier '{:?}' at {:?}", *op, expr.location),
                };
                let first = self.typecheck_apply(&expr.location, subs, op_type, &mut **lhs);
                self.typecheck_apply(&expr.location, subs, first, &mut **rhs)
            }
            Lambda(ref arg, ref mut body) => {
                let mut arg_type = self.new_var();
                let mut result = typ::function_type_(arg_type.clone(), self.new_var());

                self.typecheck_pattern(&expr.location, subs, arg, &mut arg_type);
                let body_type = self.typecheck(&mut **body, subs);
                with_arg_return(&mut result, |_, return_type| {
                    *return_type = body_type.clone();
                });
                result
            }
            Let(ref mut bindings, ref mut body) => {
                self.typecheck_local_bindings(
                    subs,
                    &mut BindingsWrapper {
                        value: &mut **bindings,
                    },
                );
                self.apply_locals(subs);
                self.typecheck(&mut **body, subs)
            }
            Case(ref mut case_expr, ref mut alts) => {
                let mut match_type = self.typecheck(&mut **case_expr, subs);
                self.typecheck_pattern(
                    &alts[0].pattern.location,
                    subs,
                    &alts[0].pattern.node,
                    &mut match_type,
                );
                match *&mut alts[0].where_bindings {
                    Some(ref mut bindings) => self.typecheck_local_bindings(
                        subs,
                        &mut BindingsWrapper {
                            value: &mut **bindings,
                        },
                    ),
                    None => (),
                }
                let mut alt0_ = self.typecheck_match(&mut alts[0].matches, subs);
                for alt in alts.iter_mut().skip(1) {
                    self.typecheck_pattern(
                        &alt.pattern.location,
                        subs,
                        &alt.pattern.node,
                        &mut match_type,
                    );
                    match alt.where_bindings {
                        Some(ref mut bindings) => self.typecheck_local_bindings(
                            subs,
                            &mut BindingsWrapper {
                                value: &mut **bindings,
                            },
                        ),
                        None => (),
                    }
                    let mut alt_type = self.typecheck_match(&mut alt.matches, subs);
                    unify_location(self, subs, &alt.pattern.location, &mut alt0_, &mut alt_type);
                }
                alt0_
            }
            IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let mut p = self.typecheck(&mut **pred, subs);
                unify_location(self, subs, &expr.location, &mut p, &mut typ::bool_type());
                let mut t = self.typecheck(&mut **if_true, subs);
                let mut f = self.typecheck(&mut **if_false, subs);
                unify_location(self, subs, &expr.location, &mut t, &mut f);
                t
            }
            Do(ref mut bindings, ref mut last_expr) => {
                let mut previous =
                    self.new_var_kind(Kind::Function(box Kind::Star, box Kind::Star));
                self.constraints.insert(
                    previous.var().clone(),
                    vec![Name {
                        name: intern("Monad"),
                        uid: 0,
                    }],
                );
                previous = Type::Application(box previous, box self.new_var());
                for bind in bindings.iter_mut() {
                    match *bind {
                        DoBinding::DoExpr(ref mut e) => {
                            let mut typ = self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut typ, &mut previous);
                        }
                        DoBinding::DoLet(ref mut bindings) => {
                            self.typecheck_local_bindings(
                                subs,
                                &mut BindingsWrapper {
                                    value: &mut **bindings,
                                },
                            );
                            self.apply_locals(subs);
                        }
                        DoBinding::DoBind(ref mut pattern, ref mut e) => {
                            let mut typ = self.typecheck(e, subs);
                            unify_location(self, subs, &e.location, &mut typ, &mut previous);
                            let inner_type = match typ {
                                Type::Application(_, ref mut t) => t,
                                _ => panic!("Not a monadic type: {:?}", typ),
                            };
                            self.typecheck_pattern(
                                &pattern.location,
                                subs,
                                &pattern.node,
                                &mut **inner_type,
                            );
                        }
                    }
                    match previous {
                        Type::Application(ref mut _monad, ref mut typ) => {
                            **typ = self.new_var();
                        }
                        _ => panic!(),
                    }
                }
                let mut typ = self.typecheck(&mut **last_expr, subs);
                unify_location(self, subs, &last_expr.location, &mut typ, &mut previous);
                typ
            }
            TypeSig(ref mut expr, ref mut qualified_type) => {
                let mut typ = self.typecheck(&mut **expr, subs);
                self.freshen_qualified_type(qualified_type, HashMap::new());
                match_or_fail(
                    self,
                    subs,
                    &expr.location,
                    &mut typ,
                    &mut qualified_type.value,
                );
                typ
            }
            Paren(ref mut expr) => self.typecheck(&mut **expr, subs),
        };
        tracing::debug!("{:?}\nas\n{:?}", &expr, &x);
        expr.typ = x.clone();
        x
    }
    fn typecheck_apply(
        &mut self,
        location: &Location,
        subs: &mut Substitution,
        mut func_type: TcType,
        arg: &mut TypedExpr<Name>,
    ) -> TcType {
        let arg_type = self.typecheck(arg, subs);
        let mut result = typ::function_type_(arg_type, self.new_var());
        unify_location(self, subs, location, &mut func_type, &mut result);
        result = match result {
            Type::Application(_, x) => *x,
            _ => panic!(
                "Must be a type application (should be a function type), found {:?}",
                result
            ),
        };
        result
    }
    ///Typechecks a pattern.
    ///Checks that the pattern has the type 'match_type' and adds all variables in the pattern.
    fn typecheck_pattern(
        &mut self,
        location: &Location,
        subs: &mut Substitution,
        pattern: &Pattern<Name>,
        match_type: &mut TcType,
    ) {
        match pattern {
            &Pattern::Identifier(ref ident) => {
                self.local_types
                    .insert(ident.clone(), qualified(vec![], match_type.clone()));
            }
            &Pattern::Number(_) => {
                let mut typ = typ::int_type();
                unify_location(self, subs, location, &mut typ, match_type);
            }
            &Pattern::Constructor(ref ctorname, ref patterns) => {
                let mut t = self.fresh(ctorname).unwrap_or_else(|| {
                    panic!(
                        "Undefined constructer '{:?}' when matching pattern",
                        *ctorname
                    )
                });
                let mut data_type = get_returntype(&t);

                unify_location(self, subs, location, &mut data_type, match_type);
                replace(&mut self.constraints, &mut t, subs);
                self.apply_locals(subs);
                self.pattern_rec(0, location, subs, &**patterns, &mut t);
            }
            &Pattern::WildCard => {}
        }
    }
    ///Walks through the arguments of a pattern and typechecks each of them.
    fn pattern_rec(
        &mut self,
        i: usize,
        location: &Location,
        subs: &mut Substitution,
        patterns: &[Pattern<Name>],
        func_type: &mut TcType,
    ) {
        if i < patterns.len() {
            let p = &patterns[i];
            with_arg_return(func_type, |arg_type, return_type| {
                self.typecheck_pattern(location, subs, p, arg_type);
                self.pattern_rec(i + 1, location, subs, patterns, return_type);
            });
        }
    }

    ///Typechecks a group of bindings such as
    ///map f (x:xs) = ...
    ///map f [] = ...
    fn typecheck_binding_group(&mut self, subs: &mut Substitution, bindings: &mut [Binding<Name>]) {
        tracing::debug!(
            "Begin typecheck {:?} :: {:?}",
            &bindings[0].name,
            &bindings[0].typ
        );
        let mut argument_types: Vec<_> = (0..bindings[0].arguments.len())
            .map(|_| self.new_var())
            .collect();
        let type_var = match bindings[0].typ.value {
            Type::Variable(ref var) => Some(var.clone()),
            _ => None,
        };
        let mut previous_type = None;
        for bind in bindings.iter_mut() {
            if argument_types.len() != bind.arguments.len() {
                panic!(
                    "Binding {:?} do not have the same number of arguments",
                    bind.name
                ); //TODO: re add location
            }
            for (arg, typ) in bind.arguments.iter_mut().zip(argument_types.iter_mut()) {
                self.typecheck_pattern(&Location::eof(), subs, arg, typ);
            }
            match bind.where_bindings {
                Some(ref mut bindings) => self.typecheck_local_bindings(
                    subs,
                    &mut BindingsWrapper {
                        value: &mut **bindings,
                    },
                ),
                None => (),
            }
            let mut typ = self.typecheck_match(&mut bind.matches, subs);
            fn make_function(arguments: &[TcType], expr: &TcType) -> TcType {
                if arguments.len() == 0 {
                    expr.clone()
                } else {
                    typ::function_type_(arguments[0].clone(), make_function(&arguments[1..], expr))
                }
            }
            typ = make_function(argument_types.as_ref(), &typ);
            match previous_type {
                Some(mut prev) => {
                    unify_location(self, subs, bind.matches.location(), &mut typ, &mut prev)
                }
                None => (),
            }
            replace(&mut self.constraints, &mut typ, subs);
            previous_type = Some(typ);
        }
        let mut final_type = previous_type.unwrap();
        //HACK, assume that if the type declaration is only a variable it has no type declaration
        //In that case we need to unify that variable to 'typ' to make sure that environment becomes updated
        //Otherwise a type declaration exists and we need to do a match to make sure that the type is not to specialized
        if type_var.is_none() {
            match_or_fail(
                self,
                subs,
                &Location::eof(),
                &mut final_type,
                &bindings[0].typ.value,
            );
        } else {
            unify_location(
                self,
                subs,
                &Location::eof(),
                &mut final_type,
                &mut bindings[0].typ.value,
            );
        }
        match type_var {
            Some(var) => {
                subs.subs.insert(var, final_type);
            }
            None => (),
        }
        for bind in bindings.iter_mut() {
            match bind.matches {
                Match::Simple(ref mut e) => self.substitute(subs, e),
                Match::Guards(ref mut gs) => {
                    for g in gs.iter_mut() {
                        self.substitute(subs, &mut g.predicate);
                        self.substitute(subs, &mut g.expression);
                    }
                }
            }
        }
        tracing::debug!(
            "End typecheck {:?} :: {:?}",
            &bindings[0].name,
            &bindings[0].typ
        );
    }

    ///Typechecks a set of bindings which may be mutually recursive
    ///Takes the minimum age that a variable created for this group can have, the current substitution, a set of bindings,
    ///and a global indicating wheter the bindings are global (true if at the module level, false otherwise, ex. 'let' binding)
    pub fn typecheck_mutually_recursive_bindings(
        &mut self,
        start_var_age: isize,
        subs: &mut Substitution,
        bindings: &mut dyn Bindings,
        is_global: bool,
    ) {
        let graph = build_graph(bindings);
        let groups = strongly_connected_components(&graph);

        for group in groups.iter() {
            for index in group.iter() {
                let bind_index = graph.get_vertex(*index).value;
                let binds = bindings.get_mut(bind_index);
                for bind in binds.iter_mut() {
                    if bind.typ.value == Type::<Name>::new_var(intern("a")) {
                        bind.typ.value = self.new_var();
                    }
                }
                if is_global {
                    self.named_types
                        .insert(binds[0].name.clone(), binds[0].typ.clone());
                } else {
                    self.local_types
                        .insert(binds[0].name.clone(), binds[0].typ.clone());
                }
            }
            for index in group.iter() {
                {
                    let bind_index = graph.get_vertex(*index).value;
                    let binds = bindings.get_mut(bind_index);
                    self.typecheck_binding_group(subs, binds);
                }
                if is_global {
                    for index in group.iter() {
                        for bind in bindings.get_mut(graph.get_vertex(*index).value).iter() {
                            replace(
                                &mut self.constraints,
                                &mut self.named_types.get_mut(&bind.name).unwrap().value,
                                subs,
                            );
                        }
                    }
                    self.local_types.clear();
                } else {
                    self.apply_locals(subs);
                }
            }
            for index in group.iter() {
                let bind_index = graph.get_vertex(*index).value;
                let binds = bindings.get_mut(bind_index);
                for constraint in binds[0].typ.constraints.iter() {
                    self.insert_constraint(&constraint.variables[0], constraint.class.clone());
                }
                for bind in binds.iter_mut() {
                    {
                        let typ = if is_global {
                            self.named_types.get_mut(&bind.name).unwrap()
                        } else {
                            self.local_types.get_mut(&bind.name).unwrap()
                        };
                        bind.typ.value = typ.value.clone();
                        quantify(start_var_age, typ);
                    }
                    bind.typ.constraints = self.find_constraints(&bind.typ.value);
                }
                tracing::debug!("End typecheck {:?} :: {:?}", &binds[0].name, &binds[0].typ);
            }
            if is_global {
                subs.subs.clear();
                self.constraints.clear();
            }
        }
    }
    ///Typechecks a group of local bindings (such as a let expression)
    fn typecheck_local_bindings(&mut self, subs: &mut Substitution, bindings: &mut dyn Bindings) {
        let var = self.variable_age + 1;
        self.typecheck_mutually_recursive_bindings(var, subs, bindings, false);
    }
    ///Typechecks a group of global bindings.
    fn typecheck_global_bindings(
        &mut self,
        start_var_age: isize,
        subs: &mut Substitution,
        bindings: &mut dyn Bindings,
    ) {
        self.typecheck_mutually_recursive_bindings(start_var_age, subs, bindings, true);
    }

    ///Workaround to make all imported functions quantified without requiring their type variables to be generic
    fn find_fresh(&self, name: &Name) -> Option<Qualified<TcType, Name>> {
        self.local_types
            .get(name)
            .or_else(|| self.named_types.get(name))
            .map(|x| x.clone())
            .or_else(|| {
                for types in self.assemblies.iter() {
                    let v = types.find_type(name).map(|x| x.clone());
                    match v {
                        Some(mut typ) => {
                            quantify(0, &mut typ);
                            return Some(typ);
                        }
                        None => (),
                    }
                }
                None
            })
    }
    ///Instantiates new typevariables for every typevariable in the type found at 'name'
    fn fresh(&mut self, name: &Name) -> Option<TcType> {
        match self.find_fresh(name) {
            Some(mut typ) => {
                let mut subs = Substitution {
                    subs: HashMap::new(),
                };
                freshen(self, &mut subs, &mut typ);
                for c in typ.constraints.iter() {
                    self.insert_constraint(&c.variables[0], c.class.clone());
                }
                Some(typ.value)
            }
            None => None,
        }
    }

    fn insert_constraint(&mut self, var: &TypeVariable, classname: Name) {
        let mut constraints = self.constraints.remove(var).unwrap_or(Vec::new());
        self.insert_constraint_(&mut constraints, classname);
        self.constraints.insert(var.clone(), constraints);
    }
    fn insert_constraint_(&mut self, constraints: &mut Vec<Name>, classname: Name) {
        let mut ii = 0;
        while ii < constraints.len() {
            if constraints[ii] == classname
                || self.exists_as_super_class(constraints[ii], classname)
            {
                //'classname' was already in the list, or existed as a sub class to the element
                return;
            }
            if self.exists_as_super_class(classname, constraints[ii]) {
                //There is already a constraint which is a super class of classname,
                //replace that class with this new one
                constraints[ii] = classname;
                return;
            }
            ii += 1;
        }
        constraints.push(classname);
    }

    ///Checks if 'classname' exists as a super class to any
    fn exists_as_super_class(&self, constraint: Name, classname: Name) -> bool {
        match self.find_class_constraints(constraint) {
            Some(constraints) => constraints.iter().any(|super_class| {
                super_class.class == classname
                    || self.exists_as_super_class(super_class.class, classname)
            }),
            None => false,
        }
    }
}

///Searches through a type, comparing it with the type on the identifier, returning all the specialized constraints
pub fn find_specialized_instances(
    typ: &TcType,
    actual_type: &TcType,
    constraints: &[Constraint<Name>],
) -> Vec<(Name, TcType)> {
    tracing::debug!(
        "Finding specialization {:?} => {:?} <-> {:?}",
        constraints,
        typ,
        actual_type
    );
    let mut result = Vec::new();
    find_specialized(&mut result, actual_type, typ, constraints);
    if constraints.len() == 0 {
        panic!(
            "Could not find the specialized instance between {:?} <-> {:?}",
            typ, actual_type
        );
    }
    result
}
fn find_specialized(
    result: &mut Vec<(Name, TcType)>,
    actual_type: &TcType,
    typ: &TcType,
    constraints: &[Constraint<Name>],
) {
    match (actual_type, typ) {
        (_, &Type::Variable(ref var)) => {
            for c in constraints.iter().filter(|c| c.variables[0] == *var) {
                if result.iter().find(|x| x.0 == c.class) == None {
                    result.push((c.class.clone(), actual_type.clone()));
                }
            }
        }
        (&Type::Application(ref lhs1, ref rhs1), &Type::Application(ref lhs2, ref rhs2)) => {
            find_specialized(result, &**lhs1, &**lhs2, constraints);
            find_specialized(result, &**rhs1, &**rhs2, constraints);
        }
        (_, &Type::Generic(ref var)) => {
            for c in constraints.iter().filter(|c| c.variables[0] == *var) {
                if result.iter().find(|x| x.0 == c.class) == None {
                    result.push((c.class.clone(), actual_type.clone()));
                }
            }
        }
        _ => (),
    }
}

///Quantifies all type variables with an age greater that start_var_age
///A quantified variable will when it is instantiated have new type variables
fn quantify(start_var_age: isize, typ: &mut Qualified<TcType, Name>) {
    fn quantify_(start_var_age: isize, typ: &mut TcType) {
        let x = match *typ {
            Type::Variable(ref id) if id.age >= start_var_age => Some(id.clone()),
            Type::Application(ref mut lhs, ref mut rhs) => {
                quantify_(start_var_age, &mut **lhs);
                quantify_(start_var_age, &mut **rhs);
                None
            }
            _ => None,
        };
        match x {
            Some(var) => *typ = Type::Generic(var),
            None => (),
        }
    }
    for constraint in typ.constraints.iter_mut() {
        if constraint.variables[0].age > start_var_age {
            //constraint.variables[0] = Type::Generic(constraint.variables[0].clone())
        }
    }
    quantify_(start_var_age, &mut typ.value);
}

///Replaces all occurences of 'var' in 'typ' with the the type 'replacement'
pub fn replace_var(typ: &mut TcType, var: &TypeVariable, replacement: &TcType) {
    let new = match *typ {
        Type::Variable(ref v) => {
            if v == var {
                Some(replacement)
            } else {
                None
            }
        }
        Type::Constructor(_) => None,
        Type::Application(ref mut lhs, ref mut rhs) => {
            replace_var(&mut **lhs, var, replacement);
            replace_var(&mut **rhs, var, replacement);
            None
        }
        Type::Generic(_) => panic!("replace_var called on Generic"),
    };
    match new {
        Some(x) => {
            *typ = x.clone();
        }
        None => (),
    }
}
///Returns true if the type is a function
fn is_function(typ: &TcType) -> bool {
    match *typ {
        Type::Application(ref lhs, _) => match **lhs {
            Type::Application(ref lhs, _) => match **lhs {
                Type::Constructor(ref op) => op.name == intern("->"),
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }
}
///Extracts the final return type of a type
fn get_returntype(typ: &TcType) -> TcType {
    match typ {
        &Type::Application(_, ref rhs) => {
            if is_function(typ) {
                get_returntype(&**rhs)
            } else {
                typ.clone()
            }
        }
        _ => typ.clone(),
    }
}

///Replace all typevariables using the substitution 'subs'
fn replace(
    constraints: &mut HashMap<TypeVariable, Vec<Name>>,
    old: &mut TcType,
    subs: &Substitution,
) {
    let replaced = match *old {
        Type::Variable(ref id) => subs.subs.get(id).map(|new| new.clone()),
        Type::Application(ref mut lhs, ref mut rhs) => {
            replace(constraints, &mut **lhs, subs);
            replace(constraints, &mut **rhs, subs);
            None
        }
        _ => None, //panic!("replace called on Generic")
    };
    match replaced {
        Some(x) => *old = x,
        None => (),
    }
}

///Checks whether a typevariable occurs in another type
fn occurs(type_var: &TypeVariable, in_type: &TcType) -> bool {
    match in_type {
        &Type::Variable(ref var) => type_var.id == var.id,
        &Type::Application(ref lhs, ref rhs) => {
            occurs(type_var, &**lhs) || occurs(type_var, &**rhs)
        }
        _ => false,
    }
}

///Freshen creates new type variables at every position where Type::Generic(..) appears.
fn freshen(env: &mut TypeEnvironment, subs: &mut Substitution, typ: &mut Qualified<TcType, Name>) {
    tracing::debug!("Freshen {:?}", &typ);
    fn freshen_(
        env: &mut TypeEnvironment,
        subs: &mut Substitution,
        constraints: &[Constraint<Name>],
        typ: &mut TcType,
    ) {
        let result = match *typ {
            Type::Generic(ref id) => freshen_var(env, subs, constraints, id),
            Type::Application(ref mut lhs, ref mut rhs) => {
                freshen_(env, subs, constraints, &mut **lhs);
                freshen_(env, subs, constraints, &mut **rhs);
                None
            }
            _ => None,
        };
        match result {
            Some(x) => *typ = x,
            None => (),
        }
    }
    freshen_(env, subs, &*typ.constraints, &mut typ.value);
    for constraint in typ.constraints.iter_mut() {
        match subs.subs.get(&constraint.variables[0]) {
            Some(new) => constraint.variables[0] = new.var().clone(),
            None => (),
        }
    }
}
///Walks through a type and updates it with new type variables.
fn freshen_all(env: &mut TypeEnvironment, subs: &mut Substitution, typ: &mut TcType) {
    let result = match *typ {
        Type::Variable(ref id) => freshen_var(env, subs, &[], id),
        Type::Application(ref mut lhs, ref mut rhs) => {
            freshen_all(env, subs, &mut **lhs);
            freshen_all(env, subs, &mut **rhs);
            None
        }
        _ => None,
    };
    match result {
        Some(x) => *typ = x,
        None => (),
    }
}
///Updates the variable var, also making sure the constraints are updated appropriately
fn freshen_var(
    env: &mut TypeEnvironment,
    subs: &mut Substitution,
    constraints: &[Constraint<Name>],
    id: &TypeVariable,
) -> Option<TcType> {
    subs.subs.get(id).map(|var| var.clone()).or_else(|| {
        let mut new = env.new_var_kind(id.kind.clone());
        match new {
            Type::Variable(ref mut v) => v.age = id.age,
            _ => (),
        }
        subs.subs.insert(id.clone(), new.clone());
        {
            let constraints_for_id = constraints.iter().filter(|c| c.variables[0] == *id);
            //Add all the constraints to he environment for the 'new' variable
            for c in constraints_for_id {
                env.insert_constraint(new.var(), c.class.clone());
            }
        }
        Some(new)
    })
}

///Takes two types and attempts to make them the same type
fn unify_location(
    env: &mut TypeEnvironment,
    subs: &mut Substitution,
    location: &Location,
    lhs: &mut TcType,
    rhs: &mut TcType,
) {
    tracing::debug!("{:?} Unifying {:?} <-> {:?}", location, &lhs, &rhs);
    match unify(env, subs, lhs, rhs) {
        Ok(()) => (),
        Err(error) => env.errors.insert(TypeErrorInfo {
            location: location.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            error: error,
        }),
    }
}

#[derive(Debug)]
struct TypeErrorInfo {
    location: Location,
    lhs: TcType,
    rhs: TcType,
    error: Error,
}

#[derive(Debug)]
enum Error {
    UnifyFail(TcType, TcType),
    RecursiveUnification,
    WrongArity(TcType, TcType),
    MissingInstance(InternedStr, TcType, TypeVariable),
}

impl fmt::Display for TypeErrorInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.error {
            Error::UnifyFail(ref l, ref r) =>
                write!(f, "{} Error: Could not unify types\n{}\nand\n{}\nin types\n{}\nand\n{}",
                    self.location, l, r, self.lhs, self.rhs),
            Error::RecursiveUnification =>
                write!(f, "{} Error: Recursive unification between {}\nand\n{}",
                    self.location, self.lhs, self.rhs),
            Error::WrongArity(ref l, ref r) =>
                write!(f, "{} Error: Types do not have the same arity.\n{} <-> {}\n{} <-> {}\n{}\nand\n{}"
                    , self.location, l, r, l.kind(), r.kind(), self.lhs, self.rhs),
            Error::MissingInstance(ref class, ref typ, ref id) =>
                write!(f, "{} Error: The instance {} {} was not found as required by {} when unifying {}\nand\n{}",
                    self.location, class, typ, id, self.lhs, self.rhs)
        }
    }
}

///Tries to bind the type to the variable.
///Returns Ok if the binding was possible.
///Returns Error if the binding was not possible and the reason for the error.
fn bind_variable(
    env: &mut TypeEnvironment,
    subs: &mut Substitution,
    var: &TypeVariable,
    typ: &TcType,
) -> Result<(), Error> {
    match *typ {
        Type::Variable(ref var2) => {
            if var != var2 {
                subs.subs.insert(var.clone(), typ.clone());
                for (_, v) in subs.subs.iter_mut() {
                    replace_var(v, var, typ);
                }
                match env.constraints.remove(var) {
                    Some(constraints) => {
                        for c in constraints.iter() {
                            env.insert_constraint(var2, c.clone());
                        }
                    }
                    None => (),
                }
            }
            Ok(())
        }
        _ => {
            if occurs(var, typ) {
                return Err(Error::RecursiveUnification);
            } else if var.kind != *typ.kind() {
                return Err(Error::WrongArity(Type::Variable(var.clone()), typ.clone()));
            } else {
                for (_, replaced) in subs.subs.iter_mut() {
                    replace_var(replaced, var, typ);
                }
                subs.subs.insert(var.clone(), typ.clone());
                let mut new_constraints = Vec::new();
                match env.constraints.get(var) {
                    Some(constraints) => {
                        for c in constraints.iter() {
                            let result = env.has_instance(*c, typ, &mut new_constraints);
                            match result {
                                Err(missing_instance) => {
                                    match *typ {
                                        Type::Constructor(ref op) => {
                                            if c.name == intern("Num")
                                                && (op.name == intern("Int")
                                                    || op.name == intern("Double"))
                                                && *typ.kind() == Kind::Star
                                            {
                                                continue;
                                            } else if c.name == intern("Fractional")
                                                && intern("Double") == op.name
                                                && *typ.kind() == Kind::Star
                                            {
                                                continue;
                                            }
                                        }
                                        _ => (),
                                    }
                                    return Err(Error::MissingInstance(
                                        missing_instance,
                                        typ.clone(),
                                        var.clone(),
                                    ));
                                }
                                Ok(()) => (),
                            }
                        }
                    }
                    _ => (),
                }
                for constraint in new_constraints.into_iter() {
                    env.insert_constraint(&constraint.variables[0], constraint.class)
                }
                Ok(())
            }
        }
    }
}

///Tries to unify two types, updating the substition as well as the types directly with
///the new type values.
fn unify(
    env: &mut TypeEnvironment,
    subs: &mut Substitution,
    lhs: &mut TcType,
    rhs: &mut TcType,
) -> Result<(), Error> {
    match (lhs, rhs) {
        (
            &mut Type::Application(ref mut l1, ref mut r1),
            &mut Type::Application(ref mut l2, ref mut r2),
        ) => unify(env, subs, &mut **l1, &mut **l2).and_then(|_| {
            replace(&mut env.constraints, &mut **r1, subs);
            replace(&mut env.constraints, &mut **r2, subs);
            unify(env, subs, &mut **r1, &mut **r2)
        }),
        (&mut Type::Variable(ref mut lhs), &mut Type::Variable(ref mut rhs)) => {
            //If both are variables we choose that they younger variable is replaced by the oldest
            //This is because when doing the quantifying, only variables that are created during
            //the inference of mutually recursive bindings should be quantified, but if a newly
            //created variable is unified with one from an outer scope we need to prefer the older
            //so that the variable does not get quantified
            if lhs.age > rhs.age {
                let x = bind_variable(env, subs, lhs, &Type::Variable(rhs.clone()));
                if x.is_ok() {
                    *lhs = rhs.clone();
                }
                x
            } else {
                let x = bind_variable(env, subs, rhs, &Type::Variable(lhs.clone()));
                if x.is_ok() {
                    *rhs = lhs.clone();
                }
                x
            }
        }
        (&mut Type::Constructor(ref lhs), &mut Type::Constructor(ref rhs)) => {
            if lhs.name == rhs.name {
                Ok(())
            } else {
                Err(Error::UnifyFail(
                    Type::Constructor(lhs.clone()),
                    Type::Constructor(rhs.clone()),
                ))
            }
        }
        (lhs, rhs) => {
            let x = match lhs {
                &mut Type::Variable(ref mut var) => bind_variable(env, subs, var, rhs),
                lhs => {
                    let y = match rhs {
                        &mut Type::Variable(ref mut var) => bind_variable(env, subs, var, lhs),
                        _ => return Err(Error::UnifyFail(lhs.clone(), rhs.clone())),
                    };
                    if y.is_ok() {
                        *rhs = lhs.clone();
                    }
                    return y;
                }
            };
            if x.is_ok() {
                *lhs = rhs.clone();
            }
            x
        }
    }
}

fn match_or_fail(
    env: &mut TypeEnvironment,
    subs: &mut Substitution,
    location: &Location,
    lhs: &mut TcType,
    rhs: &TcType,
) {
    tracing::debug!("Match {:?} --> {:?}", &lhs, &rhs);
    match match_(env, subs, lhs, rhs) {
        Ok(()) => (),
        Err(error) => env.errors.insert(TypeErrorInfo {
            location: location.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            error: error,
        }),
    }
}
///Match performs matching which is walks through the same process as unify but only allows
///the updates to be one way (such as between a type and the type in a type signature).
fn match_(
    env: &mut TypeEnvironment,
    subs: &mut Substitution,
    lhs: &mut TcType,
    rhs: &TcType,
) -> Result<(), Error> {
    match (lhs, rhs) {
        (&mut Type::Application(ref mut l1, ref mut r1), &Type::Application(ref l2, ref r2)) => {
            match_(env, subs, &mut **l1, &**l2).and_then(|_| {
                replace(&mut env.constraints, &mut **r1, subs);
                match_(env, subs, &mut **r1, &**r2)
            })
        }
        (&mut Type::Variable(ref mut lhs), &Type::Variable(ref rhs)) => {
            let x = bind_variable(env, subs, lhs, &mut Type::Variable(rhs.clone()));
            *lhs = rhs.clone();
            x
        }
        (&mut Type::Constructor(ref lhs), &Type::Constructor(ref rhs)) => {
            if lhs.name == rhs.name {
                Ok(())
            } else {
                Err(Error::UnifyFail(
                    Type::Constructor(lhs.clone()),
                    Type::Constructor(rhs.clone()),
                ))
            }
        }
        (lhs, rhs) => {
            let x = match lhs {
                &mut Type::Variable(ref mut var) => bind_variable(env, subs, var, rhs),
                _ => return Err(Error::UnifyFail(lhs.clone(), rhs.clone())),
            };
            *lhs = rhs.clone();
            x
        }
    }
}

///Creates a graph containing a vertex for each binding and edges from every binding to every other
///binding that it references
fn build_graph(bindings: &dyn Bindings) -> Graph<(usize, usize)> {
    let mut graph = Graph::new();
    let mut map = HashMap::new();
    bindings.each_binding(&mut |binds, i| {
        let index = graph.new_vertex(i);
        map.insert(binds[0].name.clone(), index);
    });
    bindings.each_binding(&mut |binds, _| {
        for bind in binds.iter() {
            match bind.matches {
                Match::Simple(ref e) => add_edges(&mut graph, &map, map[&bind.name], e),
                Match::Guards(ref gs) => {
                    for g in gs.iter() {
                        add_edges(&mut graph, &map, map[&bind.name], &g.predicate);
                        add_edges(&mut graph, &map, map[&bind.name], &g.expression);
                    }
                }
            }
        }
    });
    graph
}

///Adds an edge for each identifier which refers to a binding in the graph
fn add_edges<T: 'static>(
    graph: &mut Graph<T>,
    map: &HashMap<Name, VertexIndex>,
    function_index: VertexIndex,
    expr: &TypedExpr<Name>,
) {
    struct EdgeVisitor<'a, T: 'a> {
        graph: &'a mut Graph<T>,
        map: &'a HashMap<Name, VertexIndex>,
        function_index: VertexIndex,
    }
    impl<'a, T: 'static> Visitor<Name> for EdgeVisitor<'a, T> {
        fn visit_expr(&mut self, expr: &TypedExpr<Name>) {
            match expr.expr {
                Identifier(ref n) => match self.map.get(n) {
                    Some(index) => self.graph.connect(self.function_index, *index),
                    None => (),
                },
                _ => walk_expr(self, expr),
            }
        }
    }
    EdgeVisitor {
        graph: graph,
        map: map,
        function_index: function_index,
    }
    .visit_expr(expr)
}

///Walks through the type and calls the functions on each variable and type constructor
fn each_type<F, G, Id>(typ: &Type<Id>, mut var_fn: F, mut op_fn: G)
where
    F: FnMut(&TypeVariable),
    G: FnMut(&TypeConstructor<Id>),
{
    each_type_(typ, &mut var_fn, &mut op_fn);
}
fn each_type_<Id>(
    typ: &Type<Id>,
    var_fn: &mut dyn FnMut(&TypeVariable),
    op_fn: &mut dyn FnMut(&TypeConstructor<Id>),
) {
    match typ {
        &Type::Variable(ref var) => (*var_fn)(var),
        &Type::Constructor(ref op) => (*op_fn)(op),
        &Type::Application(ref lhs, ref rhs) => {
            each_type_(&**lhs, var_fn, op_fn);
            each_type_(&**rhs, var_fn, op_fn);
        }
        _ => (),
    }
}

///Finds the kind for the variable test and makes sure that all occurences of the variable
///has the same kind in 'typ'
///'expected' should be None if the kinds is currently unknown, otherwise the expected kind
fn find_kind(
    test: &TypeVariable,
    expected: Option<Kind>,
    typ: &TcType,
) -> Result<Option<Kind>, &'static str> {
    match *typ {
        Type::Variable(ref var) if test.id == var.id => match expected {
            Some(k) => {
                if k != var.kind {
                    Err("Kinds do not match")
                } else {
                    Ok(Some(k))
                }
            }
            None => Ok(Some(var.kind.clone())),
        },
        Type::Application(ref lhs, ref rhs) => {
            find_kind(test, expected, &**lhs).and_then(|result| find_kind(test, result, &**rhs))
        }
        _ => Ok(expected),
    }
}

///Takes a function type and calls the 'func' with the argument to the function and its
///return type.
///Returns true if the function was called.
pub fn with_arg_return<F>(func_type: &mut TcType, func: F) -> bool
where
    F: FnOnce(&mut TcType, &mut TcType),
{
    match *func_type {
        Type::Application(ref mut lhs, ref mut return_type) => match **lhs {
            Type::Application(_, ref mut arg_type) => {
                func(&mut **arg_type, &mut **return_type);
                true
            }
            _ => false,
        },
        _ => false,
    }
}


pub fn typecheck_string(module: &str) -> Result<Vec<Module<Name>>, ::std::string::String> {
    use parser::parse_string;
    parse_string(module)
        .map_err(|e| format!("{:?}", e))
        .and_then(typecheck_modules_common)
}

///Parses a module, renames and typechecks it, as well as all of its imported modules
pub fn typecheck_module(module: &str) -> Result<Vec<Module<Name>>, ::std::string::String> {
    use parser::parse_modules;
    parse_modules(module)
        .map_err(|e| format!("{:?}", e))
        .and_then(typecheck_modules_common)
}

fn typecheck_modules_common(
    modules: Vec<Module>,
) -> Result<Vec<Module<Name>>, ::std::string::String> {
    use infix::PrecedenceVisitor;
    let mut modules = rename_modules(modules).map_err(|e| format!("{}", e))?;
    let mut prec_visitor = PrecedenceVisitor::new();
    for module in modules.iter_mut() {
        prec_visitor.visit_module(module);
    }
    let result = {
        let mut env = TypeEnvironment::new();
        for module in modules.iter_mut() {
            env.typecheck_module2(module);
            env.assemblies.push(module);
        }
        env.errors.into_result(())
    };
    result
        .map(|()| modules)
        .map_err(|e| format!("{}", TypeError(e)))
}

#[cfg(test)]
pub mod tests {
    use super::*;
    pub fn identifier(i: &str) -> TypedExpr {
        TypedExpr::new(Identifier(intern(i)))
    }

    pub fn lambda(arg: &str, body: TypedExpr) -> TypedExpr {
        TypedExpr::new(Lambda(Pattern::Identifier(intern(arg)), box body))
    }

    pub fn rational(i: f64) -> TypedExpr {
        TypedExpr::new(Literal(Fractional(i)))
    }

    pub fn apply(func: TypedExpr, arg: TypedExpr) -> TypedExpr {
        TypedExpr::new(Apply(box func, box arg))
    }

    pub fn let_(bindings: Vec<Binding>, expr: TypedExpr) -> TypedExpr {
        TypedExpr::new(Let(bindings, box expr))
    }

    pub fn case(expr: TypedExpr, alts: Vec<Alternative>) -> TypedExpr {
        TypedExpr::new(Case(box expr, alts))
    }

    pub fn if_else(expr: TypedExpr, t: TypedExpr, f: TypedExpr) -> TypedExpr {
        TypedExpr::new(IfElse(box expr, box t, box f))
    }
}
