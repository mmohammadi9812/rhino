// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

extern crate rhino;
use std::{fs::File, io::Read};
use rhino::{compiler::{Instruction::*, compile_with_type_env, Assembly, compile as super_compile},
            interner::*, typecheck::TypeEnvironment};


fn compile(contents: &str) -> Assembly {
    super_compile(contents).unwrap()
}

#[test]
fn add() {
    let file = "main = primIntAdd 1 2";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[0].instructions,
        vec![PushInt(2), PushInt(1), Add, Update(0), Unwind]
    );
}

#[test]
fn add_double() {
    let file = r"add x y = primDoubleAdd x y
main = add 2. 3.";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[0].instructions,
        vec![
            Push(1),
            Eval,
            Push(0),
            Eval,
            DoubleAdd,
            Update(0),
            Pop(2),
            Unwind
        ]
    );
    assert_eq!(
        assembly.super_combinators[1].instructions,
        vec![
            PushFloat(3.),
            PushFloat(2.),
            PushGlobal(0),
            Mkap,
            Mkap,
            Eval,
            Update(0),
            Unwind
        ]
    );
}
#[test]
fn push_num_double() {
    let file = r"main = primDoubleAdd 2 3";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[0].instructions,
        vec![PushFloat(3.), PushFloat(2.), DoubleAdd, Update(0), Unwind]
    );
}

#[test]
fn application() {
    let file = r"add x y = primIntAdd x y
main = add 2 3";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[1].instructions,
        vec![
            PushInt(3),
            PushInt(2),
            PushGlobal(0),
            Mkap,
            Mkap,
            Eval,
            Update(0),
            Unwind
        ]
    );
}

#[test]
fn compile_constructor() {
    let file = r"main = primIntAdd 1 0 : []";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[0].instructions,
        vec![
            Pack(0, 0),
            PushInt(0),
            PushInt(1),
            Add,
            Pack(1, 2),
            Update(0),
            Unwind
        ]
    );
}

#[test]
fn compile_tuple() {
    let file = r"test x y = (primIntAdd 0 1, x, y)";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[0].instructions,
        vec![
            Push(1),
            Push(0),
            PushInt(1),
            PushInt(0),
            Add,
            Pack(0, 3),
            Update(0),
            Pop(2),
            Unwind
        ]
    );
}

#[test]
fn compile_case() {
    let file = r"main = case [primIntAdd 1 0] of
x:xs -> x
[] -> 2";
    let assembly = compile(file);

    assert_eq!(
        assembly.super_combinators[0].instructions,
        vec![
            Pack(0, 0),
            PushInt(0),
            PushInt(1),
            Add,
            Pack(1, 2),
            Push(0),
            CaseJump(1),
            Jump(14),
            Split(2),
            Push(1),
            Eval,
            Slide(2),
            Jump(22),
            Pop(2),
            Push(0),
            CaseJump(0),
            Jump(22),
            Split(0),
            PushInt(2),
            Slide(0),
            Jump(22),
            Pop(0),
            Slide(1),
            Eval,
            Update(0),
            Unwind
        ]
    );
}

#[test]
fn compile_class_constraints() {
    let file = r"class Test a where
test :: a -> Int

instance Test Int where
test x = x

main = test (primIntAdd 6 0)";
    let assembly = compile(file);

    let main = &assembly.super_combinators[0];
    assert_eq!(main.name.name, intern("main"));
    assert_eq!(
        main.instructions,
        vec![
            PushInt(0),
            PushInt(6),
            Add,
            PushGlobal(1),
            Mkap,
            Eval,
            Update(0),
            Unwind
        ]
    );
}

#[test]
fn compile_class_constraints_unknown() {
    let file = r"class Test a where
test :: a -> Int

instance Test Int where
test x = x

main x = primIntAdd (test x) 6";
    let assembly = compile(file);

    let main = &assembly.super_combinators[0];
    assert_eq!(main.name.name, intern("main"));
    assert_eq!(
        main.instructions,
        vec![
            PushInt(6),
            Push(1),
            PushDictionaryMember(0),
            Mkap,
            Eval,
            Add,
            Update(0),
            Pop(2),
            Unwind
        ]
    );
}

#[test]
fn compile_prelude() {
    let prelude;
    let mut type_env = TypeEnvironment::new();
    let mut contents = ::std::string::String::new();
    File::open("Prelude.hs")
        .and_then(|mut f| f.read_to_string(&mut contents))
        .unwrap();
    prelude = compile_with_type_env(&mut type_env, &[], &contents).unwrap();

    let assembly: _ =
        compile_with_type_env(&mut type_env, &[&prelude], r"main = id (primIntAdd 2 0)")
            .unwrap();

    let sc = &assembly.super_combinators[0];
    let id_index = prelude
        .super_combinators
        .iter()
        .position(|sc| sc.name.name == intern("id"))
        .unwrap();
    assert_eq!(
        sc.instructions,
        vec![
            PushInt(0),
            PushInt(2),
            Add,
            PushGlobal(id_index),
            Mkap,
            Eval,
            Update(0),
            Unwind
        ]
    );
}

#[test]
fn generics_do_not_propagate() {
    //Test that the type of 'i' does not get overwritten by the use inside the let binding
    //after typechecking the let binding, retrieving the type for 'i' the second time should
    //not make the typechecker instantiate a new variable but keep using the original one
    //This is something the typechecker should notice but for now the compiler will have to do it
    compile(
        r"
class Num a where
fromInteger :: Int -> a
instance Num Int where
fromInteger x = x
class Integral a where
rem :: a -> a -> a

instance Integral Int where
rem x y = primIntRemainder x y

showInt :: Int -> [Char]
showInt i =
let
    i2 = i `rem` 10
in showInt (i `rem` 7)
",
    );
}

#[test]
fn binding_pattern() {
    compile(
        r"
test f (x:xs) = f x : test f xs
test _ [] = []
",
    );
}

#[test]
fn newtype() {
    //Test that the newtype constructor is newer constucted
    let file = r"
newtype Test a = Test [a]
test = Test [1::Int]";
    let assembly = compile(file);

    let test = &assembly.super_combinators[0];
    assert_eq!(
        test.instructions,
        vec![Pack(0, 0), PushInt(1), Pack(1, 2), Update(0), Unwind]
    );
}

