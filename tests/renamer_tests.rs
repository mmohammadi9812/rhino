// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.


extern crate rhino;

use rhino::{interner::InternedStr, module::{Module, TypedExpr}, renamer::Name, parser::*};

pub fn rename_modules(modules: Vec<Module<InternedStr>>) -> Vec<Module<Name>> {
    rhino::renamer::rename_modules(modules).unwrap()
}
pub fn rename_module(module: Module<InternedStr>) -> Module<Name> {
    rhino::renamer::rename_module(module).unwrap()
}
pub fn rename_expr(expr: TypedExpr<InternedStr>) -> TypedExpr<Name> {
    rhino::renamer::rename_expr(expr).unwrap()
}

#[test]
#[should_panic]
fn duplicate_binding() {
    let mut parser = Parser::new(
        r"main = 1
test = []
main = 2"
            .chars(),
    );
    let module = parser.module().unwrap();
    rename_modules(vec![module]);
}
#[test]
fn import_binding() {
    let file = r"
import Prelude (id)
main = id";
    let modules = parse_string(file).unwrap_or_else(|err| panic!("{}", err));
    rename_modules(modules);
}
#[test]
#[should_panic]
fn missing_import() {
    let mut parser = Parser::new(
        r"
import Prelude ()
main = id"
            .chars(),
    );
    let module = parser.module().unwrap();
    rename_modules(vec![module]);
}
