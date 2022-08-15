#![crate_type = "bin"]
#![feature(box_syntax)]
#![cfg_attr(test, feature(test))]
#[cfg(test)]
extern crate test;

use vm::execute_main_module;

macro_rules! write_core_expr(
    ($e:expr, $f:expr, $($p:pat),*) => ({
        match $e {
            Identifier(ref s) => write!($f, "{}", *s),
            Apply(ref func, ref arg) => write!($f, "({} {})", func, *arg),
            Literal(ref l) => write!($f, "{}", *l),
            Lambda(ref arg, ref body) => write!($f, "({} -> {})", *arg, *body),
            Let(ref bindings, ref body) => {
                write!($f, "let {{\n")?;
                for bind in bindings.iter() {
                    write!($f, "; {}\n", bind)?;
                }
                write!($f, "}} in {}\n", *body)
            }
            Case(ref expr, ref alts) => {
                write!($f, "case {} of {{\n", *expr)?;
                for alt in alts.iter() {
                    write!($f, "; {}\n", alt)?;
                }
                write!($f, "}}\n")
            }
            $($p => Ok(()))*
        }
    })
);

mod builtins;
mod compiler;
mod core;
mod deriving;
mod graph;
mod infix;
mod interner;
mod lambda_lift;
mod lexer;
mod module;
mod parser;
mod renamer;
#[cfg(not(test))]
mod repl;
mod scoped_map;
mod typecheck;
mod types;
mod vm;

#[cfg(not(test))]
fn main() {
    let usage: &str = r#"
./haskell-compiler args
args:
    -l {module name} : compile and run input file
    -i               : Starts the REPL
    -h               : Print help
"#;
    let cargs: Vec<String> = std::env::args().skip(1).collect();

    if cargs.contains(&String::from("-h")) {
        println!("{}", usage);
        return;
    }

    if cargs.contains(&String::from("-l")) && cargs.contains(&String::from("-i")) {
        println!("{}", usage);
        return;
    }

    let mut f = false;

    for arg in cargs {
        if arg == "-i" {
            repl::start();
            return;
        }

        if arg == "-l" {
            f = true;
            continue;
        }

        if f {
            let result = execute_main_module(arg.as_ref()).unwrap();
            match result {
                Some(x) => println!("{:?}", x),
                None => println!("Error running module {}", arg),
            }
        }
        // TODO: let expr_str
        // let expr_str = &*matches.free[0];
        // repl::run_and_print_expr(expr_str);
    }
}
