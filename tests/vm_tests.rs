// Copyright 2022 Mohammad Mohamamdi. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.


extern crate rhino;

// TODO: use vm::VMResult::{Int, Double, Constructor};
use rhino::{interner::*, compiler::compile_with_type_env, typecheck::TypeEnvironment, vm::{
    compile_file, compile_iter, execute_main_module, execute_main_string, extract_result,
    VMResult, VM,
}};

fn execute_main<T: Iterator<Item = char>>(iterator: T) -> Option<VMResult> {
    let mut vm = VM::new();
    vm.add_assembly(compile_iter(iterator).unwrap());
    let x = vm
        .assembly
        .iter()
        .flat_map(|a| a.super_combinators.iter())
        .find(|sc| sc.name.name == intern("main"));
    match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None,
    }
}

#[test]
fn test_primitive() {
    assert_eq!(
        execute_main("main = primIntAdd 10 5".chars()),
        Some(VMResult::Int(15))
    );
    assert_eq!(
        execute_main("main = primIntSubtract 7 (primIntMultiply 2 3)".chars()),
        Some(VMResult::Int(1))
    );
    assert_eq!(
        execute_main("main = primIntDivide 10 (primIntRemainder 6 4)".chars()),
        Some(VMResult::Int(5))
    );
    assert_eq!(
        execute_main("main = primDoubleDivide 3. 2.".chars()),
        Some(VMResult::Double(1.5))
    );
    let s = r"data Bool = True | False
main = primIntLT 1 2";
    assert_eq!(
        execute_main(s.chars()),
        Some(VMResult::Constructor(0, Vec::new()))
    );
}

#[test]
fn test_function() {
    let module = r"mult2 x = primIntMultiply x 2

main = mult2 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(20)));

    let module2 = r"mult2 x = primIntMultiply x 2

add x y = primIntAdd y x

main = add 3 (mult2 10)";
    assert_eq!(execute_main(module2.chars()), Some(VMResult::Int(23)));
}
#[test]
fn test_case() {
    let module = r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
x:xs -> x
[] -> 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(246)));
}

#[test]
fn test_nested_case() {
    let module = r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
246:xs -> primIntAdd 0 246
[] -> 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(246)));
}

#[test]
fn test_nested_case2() {
    let module = r"mult2 x = primIntMultiply x 2

main = case [mult2 123, 0] of
246:[] -> primIntAdd 0 246
x:xs -> 20
[] -> 10";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(20)));
}
#[test]
fn local_function() {
    let module = r"main =
let
    f x y =
        let
            g x = primIntAdd x y
        in g (primIntAdd 1 x)
in f (primIntAdd 2 0) (primIntAdd 3 0)";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(6)));
}

#[test]
fn test_data_types() {
    let module = r"data Bool = True | False

test = False

main = case test of
False -> primIntAdd 0 0
True -> primIntAdd 1 0";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(0)));
}

#[test]
fn test_typeclasses_known_types() {
    let module = r"data Bool = True | False

class Test a where
test :: a -> Int

instance Test Int where
test x = x

instance Test Bool where
test x = case x of
    True -> 1
    False -> 0


main = primIntSubtract (test (primIntAdd 5 0)) (test True)";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(4)));
}

#[test]
fn test_typeclasses_unknown() {
    let module = r"data Bool = True | False

class Test a where
test :: a -> Int

instance Test Int where
test x = x

instance Test Bool where
test x = case x of
    True -> 1
    False -> 0

testAdd y = primIntAdd (test (primIntAdd 5 0)) (test y)

main = testAdd True";
    assert_eq!(execute_main(module.chars()), Some(VMResult::Int(6)));
}

#[test]
fn test_run_prelude() {
    let prelude = compile_file("Prelude.hs").unwrap();
    let assembly = {
        let mut type_env = TypeEnvironment::new();

        compile_with_type_env(
            &mut type_env,
            &[&prelude],
            r"add x y = primIntAdd x y
main = foldl add 0 [1,2,3,4]",
        )
        .unwrap()
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm
        .assembly
        .iter()
        .flat_map(|a| a.super_combinators.iter())
        .find(|sc| sc.name.name == intern("main"));
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None,
    };
    assert_eq!(result, Some(VMResult::Int(10)));
}

#[test]
fn instance_super_class() {
    let prelude = compile_file("Prelude.hs").unwrap();

    let assembly = {
        let mut type_env = TypeEnvironment::new();
        compile_with_type_env(
            &mut type_env,
            &[&prelude],
            "main = [primIntAdd 0 1,2,3,4] == [1,2,3]",
        )
        .unwrap()
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm
        .assembly
        .iter()
        .flat_map(|a| a.super_combinators.iter())
        .find(|sc| sc.name.name == intern("main"));
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None,
    };
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}

#[test]
fn monad_do() {
    let prelude = compile_file("Prelude.hs").unwrap();

    let assembly = {
        let mut type_env = TypeEnvironment::new();
        compile_with_type_env(
            &mut type_env,
            &[&prelude],
            "
test :: Maybe Int -> Maybe Int -> Maybe Int
test x y = do
x1 <- x
y
return (x1 + 1)

main = test (Just 4) (Just 6)",
        )
        .unwrap()
    };

    let mut vm = VM::new();
    vm.add_assembly(prelude);
    vm.add_assembly(assembly);
    let x = vm
        .assembly
        .iter()
        .flat_map(|a| a.super_combinators.iter())
        .find(|sc| sc.name.name == intern("main"));
    let result = match x {
        Some(sc) => {
            assert!(sc.arity == 0);
            let result = vm.evaluate(&*sc.instructions, sc.assembly_id);
            extract_result(result)
        }
        None => None,
    };
    assert_eq!(
        result,
        Some(VMResult::Constructor(0, vec!(VMResult::Int(5))))
    );
}

#[test]
fn import() {
    let result = execute_main_module("Test");
    assert_eq!(result, Ok(Some(VMResult::Int(6))));
}

#[test]
fn pattern_bind() {
    let result = execute_main_string(
        r"
import Prelude

test :: [Bool] -> Bool
test (True:[]) = False
test (True:y:ys) = y
test [] = False

main = test [True, True]
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Constructor(0, Vec::new())));
}
#[test]
fn pattern_guards() {
    let result = execute_main_string(
        r"
import Prelude

test :: Int -> [a] -> Int
test 2 _ = 2
test x []
| primIntLT x 0 = primIntSubtract 0 1
| primIntGT x 0 = 1
test x _ = x

main = (test 2 [], test 100 [], test 100 ['c'])

",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        result,
        Some(VMResult::Constructor(
            0,
            vec!(VMResult::Int(2), VMResult::Int(1), VMResult::Int(100))
        ))
    );
}

#[test]
fn pattern_guards_nested() {
    let result = execute_main_string(
        r"
import Prelude

test :: Int -> [Int] -> Int
test 2 _ = 2
test x (0:[])
| primIntLT x 0 = primIntSubtract 0 1
| primIntGT x 0 = 1
test x _ = x

main = (test 2 [], test 100 [0], test 100 [0, 123])

",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        result,
        Some(VMResult::Constructor(
            0,
            vec!(VMResult::Int(2), VMResult::Int(1), VMResult::Int(100))
        ))
    );
}
#[test]
fn test_class_default_function() {
    let module = r"data Bool = True | False

class Test a where
test :: a -> Int
test _ = 42
test2 :: Int

instance Test Int where
test x = x
test2 = 0

instance Test Bool where
test2 = 2

main = (test True, test (1 :: Int))";
    assert_eq!(
        execute_main(module.chars()),
        Some(VMResult::Constructor(
            0,
            vec![VMResult::Int(42), VMResult::Int(1)]
        ))
    );
}

#[test]
fn use_super_class() {
    let result = execute_main_string(
        r"
import Prelude

test x y = (x == y) || (x < y)
main = (test (0 :: Int) 2) && not (test (1 :: Int) 0)",
    )
    .unwrap_or_else(|err| panic!("{:?}", err));
    assert_eq!(result, Some(VMResult::Constructor(0, Vec::new())));
}
#[test]
fn implement_class() {
    let result = execute_main_string(
        r"
import Prelude
data AB = A | B

instance Eq AB where
(==) A A = True
(==) B B = True
(==) _ _ = False

test x y = x == y

main = A == B && test A A",
    )
    .unwrap_or_else(|err| panic!("{:?}", err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}

#[test]
fn deriving_eq() {
    let result = execute_main_string(
        r"
import Prelude
data Test = A Int | B
deriving(Eq)

main = A 0 == A 2 || A 0 == B
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}
#[test]
fn deriving_ord() {
    let result = execute_main_string(
        r"
import Prelude
data Test = A Int | B
deriving(Eq, Ord)

main = compare (A 0) (A 2) == LT && compare B (A 123) == GT
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Constructor(0, Vec::new())));
}

#[test]
fn instance_eq_list() {
    let result = execute_main_string(
        r"
import Prelude
test x y = x == y
main = test [1 :: Int] [3]
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}
#[test]
fn build_dictionary() {
    //Test that the compiler can generate code to build a dictionary at runtime
    let result = execute_main_string(
        r"
import Prelude
test :: Eq a => a -> a -> Bool
test x y = [x] == [y]
main = test [1 :: Int] [3]
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Constructor(1, Vec::new())));
}

#[test]
fn if_else() {
    let result = execute_main_string(
        r"
import Prelude

main = let
    x = 123 :: Int
in if x < 0
    then x
    else 1
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Int(1)));
}

#[test]
fn newtype() {
    let result = execute_main_string(
        r"
import Prelude
newtype Even = Even Int

makeEven :: Int -> Maybe Even
makeEven i
| i `div` 2 /= (i - 1) `div` 2 = Just (Even i)
| otherwise = Nothing

main = makeEven (100 * 3)
",
    )
    .unwrap_or_else(|err| panic!("{}", err));

    assert_eq!(
        result,
        Some(VMResult::Constructor(0, vec![VMResult::Int(300)]))
    );
}

#[test]
fn where_bindings() {
    let result = execute_main_string(
        r"
import Prelude

main = case list of
    [] -> 123
    x:xs
        | y < 10 -> 0
        | otherwise -> y
        where
        y = x + 10
where
    list = [1::Int]
",
    )
    .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, Some(VMResult::Int(11)));
}
