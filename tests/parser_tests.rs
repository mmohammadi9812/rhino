// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.


extern crate rhino;
use rhino::{parser::{Parser, parse_modules}, module::{Expr::*, LiteralData::*, *}, interner::{InternedStr, intern}, lexer::{Located, Location}};

use std::{fs::File, io::Read, path::Path};

fn op_apply(lhs: TypedExpr, op: InternedStr, rhs: TypedExpr) -> TypedExpr {
    TypedExpr::new(OpApply(Box::new(lhs), op, Box::new(rhs)))
}

fn identifier(i: &str) -> TypedExpr {
    TypedExpr::new(Identifier(intern(i)))
}

fn apply(func: TypedExpr, arg: TypedExpr) -> TypedExpr {
    TypedExpr::new(Apply(Box::new(func), Box::new(arg)))
}

fn case(expr: TypedExpr, alts: Vec<Alternative>) -> TypedExpr {
    TypedExpr::new(Case(Box::new(expr), alts))
}

fn if_else(expr: TypedExpr, t: TypedExpr, f: TypedExpr) -> TypedExpr {
    TypedExpr::new(IfElse(Box::new(expr), Box::new(t), Box::new(f)))
}


#[test]
fn simple() {
    let mut parser = Parser::new("2 + 3".chars());
    let expr = parser.expression_().unwrap();
    assert_eq!(expr, op_apply(TypedExpr::new(Literal(Integral(2))), intern("+"), TypedExpr::new(Literal(Integral(3)))));
}
#[test]
fn binding() {
    let mut parser = Parser::new("test x = x + 3".chars());
    let bind = parser.binding().unwrap();
    assert_eq!(bind.arguments, vec![Pattern::Identifier(intern("x"))]);
    assert_eq!(
        bind.matches,
        Match::Simple(op_apply(identifier("x"), intern("+"), TypedExpr::new(Literal(Integral(3)))))
    );
    assert_eq!(bind.name, intern("test"));
}

#[test]
fn double() {
    let mut parser = Parser::new("test = 3.14".chars());
    let bind = parser.binding().unwrap();
    assert_eq!(bind.matches, Match::Simple(TypedExpr::new(Literal(Fractional(3.14)))));
    assert_eq!(bind.name, intern("test"));
}

#[test]
fn parse_let() {
    let mut parser = Parser::new(
        r"
let
test = add 3 2
in test - 2"
            .chars(),
    );
    let expr = parser.expression_().unwrap();
    let bind = Binding {
        arguments: vec![],
        name: intern("test"),
        typ: Default::default(),
        matches: Match::Simple(apply(apply(identifier("add"), TypedExpr::new(Literal(Integral(3)))), TypedExpr::new(Literal(Integral(2))))),
        where_bindings: None,
    };
    assert_eq!(
        expr,
        TypedExpr::new(Let(vec![bind], Box::new(op_apply(identifier("test"), intern("-"), TypedExpr::new(Literal(Integral(2)))))))
    );
}

#[test]
fn parse_case() {
    let mut parser = Parser::new(
        r"case [] of
x:xs -> x
[] -> 2
"
        .chars(),
    );
    let expression = parser.expression_().unwrap();
    let alt = Alternative {
        pattern: Located {
            location: Location::eof(),
            node: Pattern::Constructor(
                intern(":"),
                vec![
                    Pattern::Identifier(intern("x")),
                    Pattern::Identifier(intern("xs")),
                ],
            ),
        },
        matches: Match::Simple(identifier("x")),
        where_bindings: None,
    };
    let alt2 = Alternative {
        pattern: Located {
            location: Location::eof(),
            node: Pattern::Constructor(intern("[]"), vec![]),
        },
        matches: Match::Simple(TypedExpr::new(Literal(Integral(2)))),
        where_bindings: None,
    };
    assert_eq!(expression, case(identifier("[]"), vec![alt, alt2]));
}

#[test]
fn parse_type() {
    let mut parser = Parser::new(r"(.) :: (b -> c) -> (a -> b) -> (a -> c)".chars());
    let type_decl = parser.type_declaration().unwrap();
    let a = &Type::new_var(intern("a"));
    let b = &Type::new_var(intern("b"));
    let c = &Type::new_var(intern("c"));
    let f = function_type(
        &function_type(b, c),
        &function_type(&function_type(a, b), &function_type(a, c)),
    );

    assert_eq!(type_decl.name, intern("."));
    assert_eq!(type_decl.typ.value, f);
}
#[test]
fn parse_data() {
    let mut parser = Parser::new(r"data Bool = True | False".chars());
    let data = parser.data_definition().unwrap();

    let b = qualified(vec![], bool_type());
    let t = Constructor {
        name: intern("True"),
        tag: 0,
        arity: 0,
        typ: b.clone(),
    };
    let f = Constructor {
        name: intern("False"),
        tag: 1,
        arity: 0,
        typ: b.clone(),
    };
    assert_eq!(data.typ, b);
    assert_eq!(data.constructors[0], t);
    assert_eq!(data.constructors[1], f);
}

#[test]
fn parse_data_2() {
    let mut parser = Parser::new(r"data List a = Cons a (List a) | Nil".chars());
    let data = parser.data_definition().unwrap();

    let list = Type::new_op(intern("List"), vec![Type::new_var(intern("a"))]);
    let cons = Constructor {
        name: intern("Cons"),
        tag: 0,
        arity: 2,
        typ: qualified(
            vec![],
            function_type(&Type::new_var(intern("a")), &function_type(&list, &list)),
        ),
    };
    let nil = Constructor {
        name: intern("Nil"),
        tag: 1,
        arity: 0,
        typ: qualified(vec![], list.clone()),
    };
    assert_eq!(data.typ.value, list);
    assert_eq!(data.constructors[0], cons);
    assert_eq!(data.constructors[1], nil);
}

#[test]
fn parse_tuple() {
    let mut parser = Parser::new(r"(1, x)".chars());
    let expr = parser.expression_().unwrap();

    assert_eq!(
        expr,
        apply(apply(identifier("(,)"), TypedExpr::new(Literal(Integral(1)))), identifier("x"))
    );
}

#[test]
fn parse_unit() {
    let mut parser = Parser::new(
        r"case () :: () of
() -> 1"
            .chars(),
    );
    let expr = parser.expression_().unwrap();

    assert_eq!(
        expr,
        case(
            TypedExpr::new(TypeSig(
                Box::new(identifier("()")),
                qualified(vec![], Type::new_op(intern("()"), vec![]))
            )),
            vec![Alternative {
                pattern: Located {
                    location: Location::eof(),
                    node: Pattern::Constructor(intern("()"), vec![])
                },
                matches: Match::Simple(TypedExpr::new(Literal(Integral(1)))),
                where_bindings: None
            }]
        )
    );
}

#[test]
fn test_operators() {
    let mut parser = Parser::new("1 : 2 : []".chars());
    let expr = parser.expression_().unwrap();
    assert_eq!(
        expr,
        op_apply(
            TypedExpr::new(Literal(Integral(1))),
            intern(":"),
            op_apply(TypedExpr::new(Literal(Integral(2))), intern(":"), identifier("[]"))
        )
    );
}

#[test]
fn parse_instance_class() {
    let mut parser = Parser::new(
        r"class Eq a where
(==) :: a -> a -> Bool
(/=) x y = not (x == y)
(/=) :: a -> a -> Bool


instance Eq a => Eq [a] where
(==) xs ys = undefined"
            .chars(),
    );
    let module = parser.module().unwrap();

    assert_eq!(module.classes[0].name, intern("Eq"));
    assert_eq!(module.classes[0].bindings[0].name, intern("#Eq/="));
    assert_eq!(module.classes[0].bindings.len(), 1);
    assert_eq!(module.classes[0].declarations[0].name, intern("=="));
    assert_eq!(module.classes[0].declarations[1].name, intern("/="));
    assert_eq!(module.instances[0].classname, intern("Eq"));
    assert_eq!(module.instances[0].constraints[0].class, intern("Eq"));
    assert_eq!(
        module.instances[0].typ,
        list_type(Type::new_var(intern("a")))
    );
}
#[test]
fn parse_super_class() {
    let mut parser = Parser::new(
        r"class Eq a => Ord a where
(<) :: a -> a -> Bool

"
        .chars(),
    );
    let module = parser.module().unwrap();

    let cls = &module.classes[0];
    let a = TypeVariable::new(intern("a"));
    assert_eq!(cls.name, intern("Ord"));
    assert_eq!(cls.variable, a);
    assert_eq!(cls.constraints[0].class, intern("Eq"));
    assert_eq!(cls.constraints[0].variables[0], a);
}
#[test]
fn parse_do_expr() {
    let mut parser = Parser::new(
        r"main = do
putStrLn test
s <- getContents
return s
"
        .chars(),
    );
    let module = parser.module().unwrap();

    let b = TypedExpr::new(Do(
        vec![
            DoBinding::DoExpr(apply(identifier("putStrLn"), identifier("test"))),
            DoBinding::DoBind(
                Located {
                    location: Location::eof(),
                    node: Pattern::Identifier(intern("s")),
                },
                identifier("getContents"),
            ),
        ],
        Box::new(apply(identifier("return"), identifier("s"))),
    ));
    assert_eq!(module.bindings[0].matches, Match::Simple(b));
}
#[test]
fn lambda_pattern() {
    let mut parser = Parser::new(r"\(x, _) -> x".chars());
    let expr = parser.expression_().unwrap();
    let pattern = Pattern::Constructor(
        intern("(,)"),
        vec![Pattern::Identifier(intern("x")), Pattern::WildCard],
    );
    assert_eq!(expr, TypedExpr::new(Lambda(pattern, Box::new(identifier("x")))));
}

#[test]
fn parse_imports() {
    let mut parser = Parser::new(
        r"import Hello
import World ()
import Prelude (id, sum)

"
        .chars(),
    );
    let module = parser.module().unwrap();

    assert_eq!(module.imports[0].module.as_ref(), "Hello");
    assert_eq!(module.imports[0].imports, None);
    assert_eq!(module.imports[1].module.as_ref(), "World");
    assert_eq!(module.imports[1].imports, Some(Vec::new()));
    assert_eq!(module.imports[2].module.as_ref(), "Prelude");
    assert_eq!(
        module.imports[2].imports,
        Some(vec![intern("id"), intern("sum")])
    );
}
#[test]
fn parse_module_imports() {
    let modules = parse_modules("Test").unwrap();

    assert_eq!(modules[0].name.as_ref(), "Prelude");
    assert_eq!(modules[1].name.as_ref(), "Test");
    assert_eq!(modules[1].imports[0].module.as_ref(), "Prelude");
}

#[test]
fn parse_guards() {
    let mut parser = Parser::new(
        r"
test x
| x = 1
| otherwise = 0
"
        .chars(),
    );
    let binding = parser.binding().unwrap();
    let b2 = Binding {
        arguments: vec![Pattern::Identifier(intern("x"))],
        name: intern("test"),
        typ: Default::default(),
        matches: Match::Guards(vec![
            Guard {
                predicate: identifier("x"),
                expression: TypedExpr::new(Literal(Integral(1))),
            },
            Guard {
                predicate: identifier("otherwise"),
                expression: TypedExpr::new(Literal(Integral(0))),
            },
        ]),
        where_bindings: None,
    };
    assert_eq!(binding, b2);
}

#[test]
fn parse_fixity() {
    let mut parser = Parser::new(
        r"
test x y = 2

infixr 5 `test`

infixr 6 `test2`, |<

test2 x y = 1
"
        .chars(),
    );
    let module = parser.module().unwrap();
    assert_eq!(
        module.fixity_declarations,
        [
            FixityDeclaration {
                assoc: Assoc::Right,
                precedence: 5,
                operators: vec![intern("test")]
            },
            FixityDeclaration {
                assoc: Assoc::Right,
                precedence: 6,
                operators: vec![intern("test2"), intern("|<")]
            },
        ]
    );
}

#[test]
fn deriving() {
    let mut parser = Parser::new(
        r"data Test = A | B
deriving(Eq, Debug)

dummy = 1
"
        .chars(),
    );
    let module = parser.module().unwrap();
    let data = &module.data_definitions[0];
    assert_eq!(
        data.typ,
        qualified(Vec::new(), Type::new_op(intern("Test"), Vec::new()))
    );
    assert_eq!(data.deriving, [intern("Eq"), intern("Debug")]);
}

#[test]
fn test_if_else() {
    let mut parser = Parser::new(
        r"
if test 1
then 1
else if True
    then 2
    else 3 + 2
"
        .chars(),
    );
    let e = parser.expression_().unwrap();
    assert_eq!(
        e,
        if_else(
            apply(identifier("test"), TypedExpr::new(Literal(Integral(1)))),
            TypedExpr::new(Literal(Integral(1))),
            if_else(
                identifier("True"),
                TypedExpr::new(Literal(Integral(2))),
                op_apply(TypedExpr::new(Literal(Integral(3))), intern("+"), TypedExpr::new(Literal(Integral(2))))
            )
        )
    );
}

#[test]
fn where_bindings() {
    let mut parser = Parser::new(
        r"
test = case a of
    x:y:xs -> z
        where
        z = x + y
    x:xs -> x
    [] -> z
        where z = 0
where
    a = []
"
        .chars(),
    );
    let bind = parser.binding().unwrap();
    match bind.matches {
        Match::Simple(ref e) => match e.expr {
            Case(_, ref alts) => {
                let w = alts[0].where_bindings.as_ref().expect("Expected where");
                assert_eq!(w[0].name, intern("z"));
                assert_eq!(
                    w[0].matches,
                    Match::Simple(op_apply(identifier("x"), intern("+"), identifier("y")))
                );
                let w2 = alts[2]
                    .where_bindings
                    .as_ref()
                    .expect("Expected where_bindings");
                assert_eq!(w2[0].name, intern("z"));
                assert_eq!(w2[0].matches, Match::Simple(TypedExpr::new(Literal(Integral(0)))));
            }
            _ => panic!("Expected case"),
        },
        _ => panic!("Expected simple binding"),
    }
    let binds = bind
        .where_bindings
        .as_ref()
        .expect("Expected where_bindings");
    assert_eq!(binds[0].name, intern("a"));
    assert_eq!(binds[0].matches, Match::Simple(identifier("[]")));
}

#[test]
fn parse_newtype() {
    let s = r"
newtype IntPair a = IntPair (a, Int)
";
    let module = Parser::new(s.chars()).module().unwrap();
    let a = Type::new_var(intern("a"));
    let typ = Type::new_op(intern("IntPair"), vec![a.clone()]);
    assert_eq!(module.newtypes[0].typ, qualified(Vec::new(), typ.clone()));
    assert_eq!(
        module.newtypes[0].constructor_type.value,
        function_type_(Type::new_op(intern("(,)"), vec![a, int_type()]), typ)
    );
}

#[test]
fn parse_prelude() {
    let path = &Path::new("Prelude.hs");
    let mut contents = ::std::string::String::new();
    File::open(path)
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    let mut parser = Parser::new(contents.chars());
    let module = parser.module().unwrap();

    assert!(module
        .bindings
        .iter()
        .any(|bind| bind.name == intern("foldl")));
    assert!(module.bindings.iter().any(|bind| bind.name == intern("id")));
    assert!(module
        .classes
        .iter()
        .any(|class| class.name == intern("Eq")));
}
