// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

extern crate criterion;
extern crate rhino;

use std::{path::Path, fs::File, io::Read};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rhino::{module::Module, renamer::{Name, rename_module}, typecheck::{DataTypes, TypeEnvironment}, parser, lambda_lift::do_lambda_lift, core::translate::translate_module, compiler::Compiler};

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


fn compile_bench(c: &mut Criterion) {
    let path = &Path::new("Prelude.hs");
    let mut contents = ::std::string::String::new();
    File::open(path)
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    let mut parser = parser::Parser::new(contents.chars());
    let mut module = rename_module(parser.module().unwrap()).unwrap();
    let mut type_env = TypeEnvironment::new();
    type_env.typecheck_module_(&mut module);
    let core_module = do_lambda_lift(translate_module(module));
    c.bench_function("compiler bench", |b| b.iter(|| {
        let mut compiler = Compiler::new();
        compiler.compile_module(black_box(&core_module));
    }));
}

fn lambda_lift_bench(c: &mut Criterion) {
    let path = &Path::new("Prelude.hs");
    let mut contents = ::std::string::String::new();
    File::open(path)
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    let module = do_typecheck(&contents);
    c.bench_function("lambda_lift bench",|b| b.iter(|| do_lambda_lift(translate_module(black_box(module.clone())))));
}

fn typecheck_bench(c: &mut Criterion) {
    let path = &Path::new("Prelude.hs");
    let mut contents = ::std::string::String::new();
    File::open(path)
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    let mut parser = parser::Parser::new(contents.chars());
    let module = rename_module(parser.module().unwrap()).unwrap();

    c.bench_function("typecheck bench", |b| b.iter(|| {
        let mut env = TypeEnvironment::new();
        let mut m = module.clone();
        env.typecheck_module_(black_box(&mut m));
    }));
}

fn parser_bench(c: &mut Criterion) {
    let path = &Path::new("Prelude.hs");
    let mut contents = ::std::string::String::new();
    File::open(path)
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    c.bench_function("parser bench", |b| b.iter(|| {
        let mut parser = parser::Parser::new(contents.chars());
        parser.module().unwrap();
    }));
}


criterion_group!(benches, compile_bench, lambda_lift_bench, typecheck_bench, parser_bench);
criterion_main!(benches);
