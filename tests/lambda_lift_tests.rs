// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::collections::HashSet;

extern crate rhino;
use rhino::{core::{ref_::*, translate::translate_module, *, Expr::*}, interner::*, lambda_lift::*, parser::Parser, renamer::rename_module, typecheck::TypeEnvironment};

struct CheckUniques {
    found: HashSet<Id>,
}

impl Visitor<Id> for CheckUniques {
    fn visit_binding(&mut self, bind: &Binding<Id>) {
        assert!(self.found.insert(bind.name.clone()));
        self.visit_expr(&bind.expression);
    }

    fn visit_expr(&mut self, expr: &Expr<Id>) {
        if let &Lambda(ref i, _) = expr {
            assert!(self.found.insert(i.clone()));
        }
        walk_expr(self, expr);
    }
}

#[test]
fn all_uniques() {
    let mut visitor = CheckUniques {
        found: HashSet::new(),
    };
    let mut parser = Parser::new(
        r"add x y = 2
test = 3.14
test2 x =
let
    test = 2
    f x =
        let g y = add x (f y)
        in add x test
in f x"
            .chars(),
    );
    let module = translate_module(rename_module(parser.module().unwrap()).unwrap());
    visitor.visit_module(&module);
}

fn check_args(expr: &Expr<Id>, args: &[InternedStr]) -> bool {
    match expr {
        &Lambda(ref arg, ref body) => {
            arg.name.name == args[0] && check_args(&**body, &args[1..])
        }
        _ => args.len() == 0,
    }
}

struct CheckAbstract {
    count: isize,
}

fn get_let<'a>(expr: &'a Expr<Id>, args: &mut Vec<InternedStr>) -> &'a Expr<Id> {
    match expr {
        &Apply(ref f, ref arg) => {
            match **arg {
                Identifier(ref i) => args.push(i.name.name),
                _ => panic!("Expected identifier as argument"),
            }
            get_let(&**f, args)
        }
        _ => expr,
    }
}

impl Visitor<Id> for CheckAbstract {
    fn visit_binding(&mut self, bind: &Binding<Id>) {
        if intern("f") == bind.name.name.name {
            let mut args = Vec::new();
            match get_let(&bind.expression, &mut args) {
                &Let(ref binds, ref body) => {
                    //Push the argument of the function itself
                    args.push(intern("x"));
                    assert!(check_args(&binds[0].expression, args.as_ref()));
                    assert_eq!(Identifier(binds[0].name.clone()), **body);
                }
                _ => assert!(false, "Expected Let, found {:?}", bind.expression),
            }
            self.count += 1;
        } else if intern("g") == bind.name.name.name {
            let mut args = Vec::new();
            match get_let(&bind.expression, &mut args) {
                &Let(ref binds, ref body) => {
                    args.push(intern("y"));
                    assert!(check_args(&binds[0].expression, args.as_ref()));
                    assert_eq!(Identifier(binds[0].name.clone()), **body);
                }
                _ => assert!(false, "Expected Let"),
            }
            self.count += 1;
        }
        self.visit_expr(&bind.expression);
    }
}

#[test]
fn all_free_vars() {
    let mut visitor = CheckAbstract { count: 0 };
    let mut parser = Parser::new(
        r"add x y = 2
test = 3.14
test2 x =
let
    test = 2
    f x =
        let g y = add x (f y)
        in add x test
in f x"
            .chars(),
    );
    let mut module = rhino::renamer::rename_module(parser.module().unwrap()).unwrap();
    TypeEnvironment::new()
        .typecheck_module(&mut module)
        .unwrap();
    let m = translate_module(module);
    let module = abstract_module(m);
    visitor.visit_module(&module);
    assert_eq!(visitor.count, 2);
}

struct NoLambdas;

impl<T> Visitor<T> for NoLambdas {
    fn visit_expr(&mut self, expr: &Expr<T>) {
        match expr {
            &Lambda(..) => assert!(false, "Found lambda in expression"),
            _ => (),
        }
        walk_expr(self, expr);
    }
}

#[test]
fn no_local_lambdas() {
    fn skip_lambdas<T>(expr: &Expr<T>) -> &Expr<T> {
        match expr {
            &Lambda(_, ref body) => skip_lambdas(&**body),
            _ => expr,
        }
    }

    let mut visitor = NoLambdas;
    let mut parser = Parser::new(
        r"add x y = 2
test = 3.14
test2 x =
let
    test = 2
    f x =
        let g y = add x (f y)
        in add x test
in f x"
            .chars(),
    );
    let m = translate_module(rename_module(parser.module().unwrap()).unwrap());
    let module = lift_lambdas(m);
    for bind in module.bindings.iter() {
        visitor.visit_expr(skip_lambdas(&bind.expression));
    }
}
