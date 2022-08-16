// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

extern crate rhino;

use rhino::{interner::*, module::{*, Expr::*, LiteralData::*}, renamer::{rename_expr, rename_module, Name}, typecheck::*, parser::{Parser, self}};
use std::{fs::File, io::Read, path::Path};

fn do_typecheck(input: &str) -> Module<Name> {
    do_typecheck_with(input, &[])
}

fn do_typecheck_with(input: &str, types: &[&dyn DataTypes]) -> Module<Name> {
    let mut parser = parser::Parser::new(input.chars());
    let mut module = rename_module(parser.module().unwrap()).unwrap();
    let mut env = TypeEnvironment::new();
    for t in types.iter() {
        env.add_types(*t);
    }
    env.typecheck_module_(&mut module);
    module
}

fn un_name_type(typ: Type<Name>) -> Type<InternedStr> {
    typ.map(|name| name.name)
}

fn un_name(typ: Qualified<Type<Name>, Name>) -> Qualified<Type<InternedStr>, InternedStr> {
    let Qualified {
        constraints,
        value: typ,
    } = typ;
    let constraints2: Vec<Constraint> = constraints
        .into_iter()
        .map(|c| Constraint {
            class: c.class.name,
            variables: c.variables,
        })
        .collect();
    qualified(constraints2, un_name_type(typ))
}

fn apply(func: TypedExpr, arg: TypedExpr) -> TypedExpr {
    TypedExpr::new(Apply(Box::new(func), Box::new(arg)))
}

fn lambda(arg: &str, body: TypedExpr) -> TypedExpr {
    TypedExpr::new(Lambda(Pattern::Identifier(intern(arg)), Box::new(body)))
}


#[test]
fn application() {
    let mut env = TypeEnvironment::new();
    let n = TypedExpr::new(Identifier(intern("primIntAdd")));
    let num = TypedExpr::new(Literal(Integral(1)));
    let e = apply(n, num);
    let mut expr = rename_expr(e).unwrap();
    let unary_func = function_type_(int_type(), int_type());
    env.typecheck_expr_(&mut expr);

    assert!(expr.typ == unary_func);
}

#[test]
fn typecheck_lambda() {
    let mut env = TypeEnvironment::new();
    let unary_func = function_type_(int_type(), int_type());

    let e = lambda(
        "x",
        apply(apply(TypedExpr::new(Identifier(intern("primIntAdd"))), TypedExpr::new(Identifier(intern("x")))), TypedExpr::new(Literal(Integral(1)))),
    );
    let mut expr = rename_expr(e).unwrap();
    env.typecheck_expr_(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_let() {
    let mut env = TypeEnvironment::new();
    let unary_func = function_type_(int_type(), int_type());

    //let test x = add x in test
    let unary_bind = lambda(
        "x",
        apply(apply(TypedExpr::new(Identifier(intern("primIntAdd"))), TypedExpr::new(Identifier(intern("x")))), TypedExpr::new(Literal(Integral(1)))),
    );
    let e = TypedExpr::new(Let(
        vec![Binding {
            arguments: vec![],
            name: intern("test"),
            matches: Match::Simple(unary_bind),
            typ: Default::default(),
            where_bindings: None,
        }],
        Box::new(TypedExpr::new(Identifier(intern("test"))))));
    let mut expr = rename_expr(e).unwrap();
    env.typecheck_expr_(&mut expr);

    assert_eq!(expr.typ, unary_func);
}

#[test]
fn typecheck_case() {
    let mut env = TypeEnvironment::new();
    let type_int = int_type();

    let mut parser = Parser::new(r"case [] of { x:xs -> primIntAdd x 2 ; [] -> 3}".chars());
    let mut expr = rename_expr(parser.expression_().unwrap()).unwrap();
    env.typecheck_expr_(&mut expr);

    assert_eq!(expr.typ, type_int);
    match &expr.expr {
        &Case(ref case_expr, _) => {
            assert_eq!(case_expr.typ, list_type(type_int));
        }
        _ => panic!("typecheck_case"),
    }
}

#[test]
fn typecheck_list() {
    let file = r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
x:xs -> x
[] -> 10";
    let module = do_typecheck(file);

    assert_eq!(module.bindings[1].typ.value, int_type());
}

#[test]
fn test_typecheck_string() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new("\"hello\"".chars());
    let mut expr = rename_expr(parser.expression_().unwrap()).unwrap();
    env.typecheck_expr_(&mut expr);

    assert_eq!(expr.typ, list_type(char_type()));
}

#[test]
fn typecheck_tuple() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new("(primIntAdd 0 0, \"a\")".chars());
    let mut expr = rename_expr(parser.expression_().unwrap()).unwrap();
    env.typecheck_expr_(&mut expr);

    let list = list_type(char_type());
    assert_eq!(
        expr.typ,
        Type::new_op(intern("(,)"), vec![int_type(), list])
    );
}

#[test]
fn typecheck_module_() {
    let file = r"data Bool = True | False
test x = True";
    let module = do_typecheck(file);

    let typ = function_type_(Type::new_var(intern("a")), bool_type());
    assert_eq!(module.bindings[0].typ.value, typ);
}

#[test]
fn typecheck_recursive_let() {
    let mut env = TypeEnvironment::new();

    let mut parser = Parser::new(
        r"let
a = primIntAdd 0 1
test = primIntAdd 1 2 : test2
test2 = 2 : test
b = test
in b"
            .chars(),
    );
    let mut expr = rename_expr(parser.expression_().unwrap()).unwrap();
    env.typecheck_expr_(&mut expr);

    let int_type = int_type();
    let list_type = list_type(int_type.clone());
    match &expr.expr {
        &Let(ref binds, _) => {
            assert_eq!(binds.len(), 4);
            assert_eq!(binds[0].name.as_ref(), "a");
            assert_eq!(binds[0].typ.value, int_type);
            assert_eq!(binds[1].name.as_ref(), "test");
            assert_eq!(binds[1].typ.value, list_type);
        }
        _ => panic!("Error"),
    }
}

#[test]
fn typecheck_constraints() {
    let file = r"class Test a where
test :: a -> Int

instance Test Int where
test x = 10

main = test 1";

    let module = do_typecheck(file);

    let typ = &module.bindings[0].typ.value;
    assert_eq!(typ, &int_type());
}

//Test that calling a function with constraints will propagate the constraints to
//the type of the caller
#[test]
fn typecheck_constraints2() {
    let mut parser = Parser::new(
        r"class Test a where
test :: a -> Int

instance Test Int where
test x = 10

main x y = primIntAdd (test x) (test y)"
            .chars(),
    );

    let mut module = rename_module(parser.module().unwrap()).unwrap();

    let mut env = TypeEnvironment::new();
    env.typecheck_module_(&mut module);

    let typ = &module.bindings[0].typ;
    let a = Type::new_var(intern("a"));
    let b = Type::new_var(intern("b"));
    let test = function_type_(a.clone(), function_type_(b.clone(), int_type()));
    assert_eq!(&typ.value, &test);
    assert_eq!(typ.constraints[0].class.as_ref(), "Test");
    assert_eq!(typ.constraints[1].class.as_ref(), "Test");
}

#[test]
#[should_panic]
fn typecheck_constraints_no_instance() {
    let file = r"class Test a where
test :: a -> Int

instance Test Int where
test x = 10

main = test [1]";

    do_typecheck(file);
}

#[test]
fn typecheck_super_class() {
    let mut parser = Parser::new(
        r"data Bool = True | False

class Eq a where
(==) :: a -> a -> Bool

class Eq a => Ord a where
(<) :: a -> a -> Bool

instance Eq Bool where
(==) True True = True
(==) False False = True
(==) _ _ = False

instance Ord Bool where
(<) False True = True
(<) _ _ = False

test x y = case x < y of
True -> True
False -> x == y

"
        .chars(),
    );

    let mut module = rename_module(parser.module().unwrap()).unwrap();

    let mut env = TypeEnvironment::new();
    env.typecheck_module_(&mut module);

    let typ = &module.bindings[0].typ;
    let a = Type::new_var(intern("a"));
    assert_eq!(
        typ.value,
        function_type_(a.clone(), function_type_(a.clone(), bool_type()))
    );
    assert_eq!(typ.constraints.len(), 1);
    assert_eq!(typ.constraints[0].class.as_ref(), "Ord");
}

#[test]
#[should_panic]
fn typecheck_missing_super_class() {
    let mut parser = Parser::new(
        r"data Bool = True | False

class Eq a where
(==) :: a -> a -> Bool

class Eq a => Ord a where
(<) :: a -> a -> Bool

instance Ord Bool where
(<) False True = True
(<) _ _ = False

test y = False < y

"
        .chars(),
    );

    let mut module = rename_module(parser.module().unwrap()).unwrap();

    let mut env = TypeEnvironment::new();
    env.typecheck_module_(&mut module);
}

#[test]
fn typecheck_instance_super_class() {
    let mut parser = Parser::new(
        r"data Bool = True | False

class Eq a where
(==) :: a -> a -> Bool

instance Eq a => Eq [a] where
(==) xs ys = case xs of
    x2:xs2 -> case ys of
        y2:ys2 -> (x2 == y2) && (xs2 == ys2)
        [] -> False
    [] -> case ys of
        y2:ys2 -> False
        [] -> True

(&&) :: Bool -> Bool -> Bool
(&&) x y = case x of
True -> y
False -> False
"
        .chars(),
    );

    let mut module = rename_module(parser.module().unwrap()).unwrap();

    let mut env = TypeEnvironment::new();
    env.typecheck_module_(&mut module);

    let typ = &module.instances[0].bindings[0].typ;
    let var = un_name_type(typ.value.appl().appr().appr().clone());
    let list_type = list_type(var.clone());
    assert_eq!(
        un_name(typ.clone()),
        qualified(
            vec![Constraint {
                class: intern("Eq"),
                variables: vec![var.var().clone()]
            }],
            function_type_(list_type.clone(), function_type_(list_type, bool_type()))
        )
    );
}

#[test]
fn typecheck_num_double() {
    let file = r"test x = primDoubleAdd 0 x";
    let module = do_typecheck(file);

    let typ = function_type_(double_type(), double_type());
    assert_eq!(module.bindings[0].typ.value, typ);
}

#[test]
fn typecheck_functor() {
    let file = r"data Maybe a = Just a | Nothing

class Functor f where
fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
fmap f x = case x of
    Just y -> Just (f y)
    Nothing -> Nothing

add2 x = primIntAdd x 2
main = fmap add2 (Just 3)";
    let module = do_typecheck(file);

    let main = &module.bindings[1];
    assert_eq!(
        main.typ.value,
        Type::new_op(intern("Maybe"), vec![int_type()])
    );
}
#[should_panic]
#[test]
fn typecheck_functor_error() {
    do_typecheck(
        r"data Maybe a = Just a | Nothing

class Functor f where
fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
fmap f x = case x of
    Just y -> Just (f y)
    Nothing -> Nothing

add2 x = primIntAdd x 2
main = fmap add2 3",
    );
}

#[test]
fn typecheck_prelude() {
    let path = &Path::new("Prelude.hs");
    let mut contents = ::std::string::String::new();
    File::open(path)
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    let module = do_typecheck(contents.as_ref());

    let id = module
        .bindings
        .iter()
        .find(|bind| bind.name.as_ref() == "id");
    assert!(id != None);
    let id_bind = id.unwrap();
    assert_eq!(
        id_bind.typ.value,
        function_type_(Type::new_var(intern("a")), Type::new_var(intern("a")))
    );
}

#[test]
fn typecheck_import() {
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let mut contents = ::std::string::String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut contents))
            .unwrap();
        do_typecheck(contents.as_ref())
    };

    let file = r"
test1 = map not [True, False]
test2 = id (primIntAdd 2 0)";
    let module = do_typecheck_with(file, &[&prelude as &dyn DataTypes]);

    assert_eq!(module.bindings[0].name.as_ref(), "test1");
    assert_eq!(module.bindings[0].typ.value, list_type(bool_type()));
    assert_eq!(module.bindings[1].name.as_ref(), "test2");
    assert_eq!(module.bindings[1].typ.value, int_type());
}

#[test]
fn type_declaration() {
    let input = r"
class Test a where
test :: a -> Int

instance Test Int where
test x = x

test2 :: Test a => a -> Int -> Int
test2 x y = primIntAdd (test x) y";
    let module = do_typecheck(input);

    assert_eq!(module.bindings[0].typ, module.type_declarations[0].typ);
}

#[test]
fn do_expr_simple() {
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let mut contents = ::std::string::String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut contents))
            .unwrap();
        do_typecheck(contents.as_ref())
    };

    let file = r"
test x = do
let z = [1::Int]
    y = reverse x
    t = [2::Int]
putStrLn y
";
    let module = do_typecheck_with(file, &[&prelude as &dyn DataTypes]);

    assert_eq!(
        module.bindings[0].typ.value,
        function_type_(list_type(char_type()), io(unit()))
    );
}

#[test]
fn do_expr_pattern() {
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let mut contents = ::std::string::String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut contents))
            .unwrap();
        do_typecheck(&contents)
    };

    let file = r"
test x = do
y:ys <- x
return y
";
    let module = do_typecheck_with(file, &[&prelude as &dyn DataTypes]);

    let var = Type::new_var(intern("a"));
    let t = function_type_(
        Type::new_var_args(intern("c"), vec![list_type(var.clone())]),
        Type::new_var_args(intern("c"), vec![var.clone()]),
    );
    assert_eq!(module.bindings[0].typ.value, t);
    assert_eq!(
        module.bindings[0].typ.constraints[0].class.as_ref(),
        "Monad"
    );
}

#[test]
fn binding_pattern() {
    let module = do_typecheck(
        r"
test f (x:xs) = f x : test f xs
test _ [] = []
",
    );
    let a = Type::new_var(intern("a"));
    let b = Type::new_var(intern("b"));
    let test = function_type_(
        function_type_(a.clone(), b.clone()),
        function_type_(list_type(a), list_type(b)),
    );
    assert_eq!(module.bindings[0].typ.value, test);
}

#[test]
fn guards() {
    let module = do_typecheck(
        r"

data Bool = True | False

if_ p x y
| p = x
| True = y
",
    );
    let var = Type::new_var(intern("a"));
    let test = function_type_(
        bool_type(),
        function_type_(var.clone(), function_type_(var.clone(), var.clone())),
    );
    assert_eq!(module.bindings[0].typ.value, test);
}

#[test]
fn typedeclaration_on_expression() {
    let module = do_typecheck(
        r"
test = [1,2,3 :: Int]
",
    );
    assert_eq!(module.bindings[0].typ.value, list_type(int_type()));
}

#[test]
fn deriving() {
    typecheck_string(
        r"import Prelude
data Test = Test Int
deriving(Eq)

data Test2 a = J a | N
deriving(Eq)

test x = Test 2 == Test 1 || J x == N",
    )
    .unwrap();
}

#[test]
fn instance_constraints_propagate() {
    let modules = typecheck_string(
        r"
import Prelude

test x y = [x] == [y]
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    let module = modules.last().unwrap();
    let a = Type::new_var(intern("a"));
    let cs = vec![Constraint {
        class: intern("Eq"),
        variables: vec![a.var().clone()],
    }];
    let typ = qualified(
        cs,
        function_type_(a.clone(), function_type_(a.clone(), bool_type())),
    );
    assert_eq!(un_name(module.bindings[0].typ.clone()), typ);
}

#[test]
fn newtype() {
    let modules = typecheck_string(
        r"
import Prelude
newtype Even = Even Int

makeEven i
| i `div` 2 /= (i - 1) `div` 2 = Even i
| otherwise = undefined

",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    let module = modules.last().unwrap();
    assert_eq!(
        un_name(module.bindings[0].typ.clone()),
        qualified(
            Vec::new(),
            function_type_(int_type(), Type::new_op(intern("Even"), Vec::new()))
        )
    );
}

#[test]
#[should_panic]
fn typedeclaration_to_general() {
    do_typecheck(
        r"
test x = primIntAdd 2 x :: Num a => a
",
    );
}

#[test]
#[should_panic]
fn do_expr_wrong_monad() {
    let prelude = {
        let path = &Path::new("Prelude.hs");
        let mut contents = ::std::string::String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut contents))
            .unwrap();
        do_typecheck(contents.as_ref())
    };

    let file = r"
test x = do
putStrLn x
reverse [primIntAdd 0 0, 1, 2]";
    do_typecheck_with(file, &[&prelude as &dyn DataTypes]);
}

#[test]
#[should_panic]
fn wrong_type() {
    do_typecheck(r"test = primIntAdd 2 []");
}

#[test]
#[should_panic]
fn argument_count_error() {
    do_typecheck("test = primIntAdd 2 2 3");
}
#[test]
#[should_panic]
fn case_alternative_error() {
    do_typecheck(
        r"
test = case [primIntAdd 1 2] of
[] -> primIntAdd 0 1
2 -> 1",
    );
}

#[test]
#[should_panic]
fn type_declaration_error() {
    do_typecheck(
        r"
test :: [Int] -> Int -> Int
test x y = primIntAdd x y",
    );
}

#[test]
#[should_panic]
fn all_constraints_match() {
    typecheck_string(
        r"
import Prelude

class Test a where
test :: a -> a
instance (Eq a, Test a) => Test (Maybe a) where
test x = x

test :: Test a => a -> a
test x = test x

test2 = test (Just True)",
    )
    .unwrap_or_else(|err| panic!("{}", err));
}

#[test]
#[should_panic]
fn where_binding() {
    typecheck_string(
        r"
test = case 1 :: Int of
2 -> []
x -> y
where
    y = x 1
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
}

#[test]
#[should_panic]
fn newtype_wrong_arg() {
    typecheck_string(
        r"
import Prelude
newtype IntPair a = IntPair (a, Int)

test = IntPair (True, False)

",
    )
    .unwrap_or_else(|err| panic!("{}", err));
}
