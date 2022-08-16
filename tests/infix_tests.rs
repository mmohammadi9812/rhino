// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

extern crate rhino;
use rhino::{infix::PrecedenceVisitor, interner::{InternedStr, intern}, module::{*, Expr::*, LiteralData::*},
            parser::*, renamer::Name};


fn rename_expr(expr: TypedExpr<InternedStr>) -> TypedExpr<Name> {
    rhino::renamer::rename_expr(expr).unwrap()
}

fn op_apply(lhs: TypedExpr, op: InternedStr, rhs: TypedExpr) -> TypedExpr {
    TypedExpr::new(OpApply(Box::new(lhs), op, Box::new(rhs)))
}

#[test]
fn operator_precedence() {
    let m = parse_string(
        r"import Prelude
test = 3 * 4 - 5 * 6",
    )
    .unwrap();
    let mut modules = rhino::renamer::rename_modules(m).unwrap();
    let mut v = PrecedenceVisitor::new();
    for module in modules.iter_mut() {
        v.visit_module(module);
    }
    assert_eq!(
        modules.last().unwrap().bindings[0].matches,
        Match::Simple(rename_expr(op_apply(
            op_apply(TypedExpr::new(Literal(Integral(3))), intern("*"), TypedExpr::new(Literal(Integral(4)))),
            intern("-"),
            op_apply(TypedExpr::new(Literal(Integral(5))), intern("*"), TypedExpr::new(Literal(Integral(6))))
        )))
    );
}
#[test]
fn operator_precedence_parens() {
    let m = parse_string(
        r"import Prelude
test = 3 * 4 * (5 - 6)",
    )
    .unwrap();
    let mut modules = rhino::renamer::rename_modules(m).unwrap();
    let mut v = PrecedenceVisitor::new();
    for module in modules.iter_mut() {
        v.visit_module(module);
    }
    assert_eq!(
        modules.last().unwrap().bindings[0].matches,
        Match::Simple(rename_expr(op_apply(
            op_apply(TypedExpr::new(Literal(Integral(3))), intern("*"), TypedExpr::new(Literal(Integral(4)))),
            intern("*"),
            TypedExpr::new(Paren(Box::new(op_apply(TypedExpr::new(Literal(Integral(5))), intern("-"), TypedExpr::new(Literal(Integral(6)))))))
        )))
    );
}

#[test]
fn rewrite_operators() {
    let mut expr = rename_expr(op_apply(
        TypedExpr::new(Literal(Integral(1))),
        intern("*"),
        op_apply(TypedExpr::new(Literal(Integral(2))), intern("+"), TypedExpr::new(Literal(Integral(3)))),
    ));
    PrecedenceVisitor::new().visit_expr(&mut expr);
    assert_eq!(
        expr,
        rename_expr(op_apply(
            op_apply(TypedExpr::new(Literal(Integral(1))), intern("*"), TypedExpr::new(Literal(Integral(2)))),
            intern("+"),
            TypedExpr::new(Literal(Integral(3)))
        ))
    );
}
