use core::Expr::*;
use core::*;
use renamer::typ::*;
use renamer::NameSupply;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

pub type TypeAndStr = Id;

pub fn do_lambda_lift(module: Module<TypeAndStr>) -> Module<Id> {
    lift_lambdas(abstract_module(module))
}

struct FreeVariables {
    name_supply: NameSupply,
}

fn each_pattern_variables(pattern: &Pattern<Id>, f: &mut dyn FnMut(&Name)) {
    match *pattern {
        Pattern::Identifier(ref ident) => (*f)(&ident.name),
        Pattern::Constructor(_, ref patterns) => {
            for p in patterns.iter() {
                (*f)(&p.name);
            }
        }
        _ => (),
    }
}

impl FreeVariables {
    //Walks through an expression and notes all the free variables and for each lambda, adds the
    //free variables to its arguments and performs an immediate application
    //@variables All the local variables in scope, values are how many of the name there exists
    //@free_vars The free variables for the returned expression
    fn free_variables(
        &mut self,
        variables: &mut HashMap<Name, isize>,
        free_vars: &mut HashMap<Name, TypeAndStr>,
        expr: &mut Expr<TypeAndStr>,
    ) {
        match *expr {
            Identifier(ref mut i) => {
                //If the identifier is a local, add it to the free variables
                if variables.get(&i.name).map(|x| *x > 0).unwrap_or(false) {
                    free_vars.insert(i.name.clone(), i.clone());
                }
            }
            Apply(ref mut func, ref mut arg) => {
                self.free_variables(variables, free_vars, &mut **func);
                self.free_variables(variables, free_vars, &mut **arg);
            }
            Lambda(ref mut arg, ref mut body) => {
                match variables.entry(arg.name.clone()) {
                    Entry::Vacant(entry) => {
                        entry.insert(1);
                    }
                    Entry::Occupied(mut entry) => *entry.get_mut() += 1,
                }
                self.free_variables(variables, free_vars, &mut **body);
                *variables.get_mut(&arg.name).unwrap() -= 1;
                free_vars.remove(&arg.name); //arg was not actually a free variable
            }
            Let(ref mut bindings, ref mut expr) => {
                for bind in bindings.iter() {
                    match variables.entry(bind.name.name.clone()) {
                        Entry::Vacant(entry) => {
                            entry.insert(1);
                        }
                        Entry::Occupied(mut entry) => *entry.get_mut() += 1,
                    }
                }
                let mut free_vars2 = HashMap::new();
                for bind in bindings.iter_mut() {
                    free_vars2.clear();
                    self.free_variables(variables, &mut free_vars2, &mut bind.expression);
                    //free_vars2 is the free variables for this binding
                    for (k, v) in free_vars2.iter() {
                        free_vars.insert(k.clone(), v.clone());
                    }
                    self.abstract_(&free_vars2, &mut bind.expression);
                }
                self.free_variables(variables, free_vars, &mut **expr);
                for bind in bindings.iter() {
                    *variables.get_mut(&bind.name.name).unwrap() -= 1;
                    free_vars.remove(&bind.name.name);
                }
            }
            Case(ref mut expr, ref mut alts) => {
                self.free_variables(variables, free_vars, &mut **expr);
                for alt in alts.iter_mut() {
                    each_pattern_variables(&alt.pattern, &mut |name| match variables
                        .entry(name.clone())
                    {
                        Entry::Vacant(entry) => {
                            entry.insert(1);
                        }
                        Entry::Occupied(mut entry) => *entry.get_mut() += 1,
                    });
                    self.free_variables(variables, free_vars, &mut alt.expression);
                    each_pattern_variables(&alt.pattern, &mut |name| {
                        *variables.get_mut(name).unwrap() -= 1;
                        free_vars.remove(name); //arg was not actually a free variable
                    });
                }
            }
            _ => (),
        }
    }
    ///Adds the free variables, if any, to the expression
    fn abstract_(
        &mut self,
        free_vars: &HashMap<Name, TypeAndStr>,
        input_expr: &mut Expr<TypeAndStr>,
    ) {
        if free_vars.len() != 0 {
            let mut temp = Literal(LiteralData {
                typ: Type::new_var(self.name_supply.from_str("a").name),
                value: Integral(0),
            });
            ::std::mem::swap(&mut temp, input_expr);
            let mut e = {
                let mut rhs = temp;
                let mut typ = rhs.get_type().clone();
                for (_, var) in free_vars.iter() {
                    rhs = Lambda(var.clone(), box rhs);
                    typ = function_type_(var.get_type().clone(), typ);
                }
                let id = Id::new(self.name_supply.from_str("#sc"), typ.clone(), Vec::new());
                let bind = Binding {
                    name: id.clone(),
                    expression: rhs,
                };
                Let(vec![bind], box Identifier(id))
            };
            for (_, var) in free_vars.iter() {
                e = Apply(box e, box Identifier(var.clone()));
            }
            *input_expr = e
        }
    }
}

///Lifts all lambdas in the module to the top level of the program
pub fn lift_lambdas<T>(mut module: Module<T>) -> Module<T> {
    use core::mutable::*;
    struct LambdaLifter<T> {
        out_lambdas: Vec<Binding<T>>,
    }
    impl<T> Visitor<T> for LambdaLifter<T> {
        fn visit_expr(&mut self, expr: &mut Expr<T>) {
            match *expr {
                Let(ref mut bindings, ref mut body) => {
                    let mut new_binds = Vec::new();
                    let mut bs = vec![];
                    ::std::mem::swap(&mut bs, bindings);
                    for mut bind in bs.into_iter() {
                        let is_lambda = match bind.expression {
                            Lambda(..) => true,
                            _ => false,
                        };
                        walk_expr(self, &mut bind.expression);
                        if is_lambda {
                            self.out_lambdas.push(bind);
                        } else {
                            new_binds.push(bind);
                        }
                    }
                    *bindings = new_binds;
                    self.visit_expr(&mut **body);
                }
                _ => walk_expr(self, expr),
            }
            remove_empty_let(expr);
        }
    }
    let mut visitor = LambdaLifter {
        out_lambdas: Vec::new(),
    };
    visitor.visit_module(&mut module);
    let mut temp = Vec::new();
    ::std::mem::swap(&mut temp, &mut module.bindings);
    let vec: Vec<Binding<T>> = temp
        .into_iter()
        .chain(visitor.out_lambdas.into_iter())
        .collect();
    module.bindings = vec;
    module
}
//Replaces let expressions with no binding with the expression itself
fn remove_empty_let<T>(expr: &mut Expr<T>) {
    let mut temp = unsafe { ::std::mem::MaybeUninit::<Expr<T>>::uninit().assume_init() };
    ::std::mem::swap(&mut temp, expr);
    temp = match temp {
        Let(bindings, e) => {
            if bindings.len() == 0 {
                *e
            } else {
                Let(bindings, e)
            }
        }
        temp => temp,
    };
    ::std::mem::swap(&mut temp, expr);
    ::std::mem::forget(temp);
}

///Takes a module and adds all variables which are captured into a lambda to its arguments
pub fn abstract_module(mut module: Module<TypeAndStr>) -> Module<TypeAndStr> {
    use core::mutable::*;
    impl Visitor<TypeAndStr> for FreeVariables {
        fn visit_binding(&mut self, bind: &mut Binding<TypeAndStr>) {
            let mut variables = HashMap::new();
            let mut free_vars = HashMap::new();
            self.free_variables(&mut variables, &mut free_vars, &mut bind.expression);
        }
    }
    let mut this = FreeVariables {
        name_supply: NameSupply::new(),
    };
    this.visit_module(&mut module);
    module
}
