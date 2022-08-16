extern crate clap;
use clap::{Command, arg};

fn main() {
    tracing_subscriber::fmt::init();
    
    let cmd = Command::new("rhino")
    .about("A (mostly functional) haskell compiler in rust")
    .version("0.2.0")
    .arg_required_else_help(true)
    .arg(arg!(<INPUT> "the input haskell file").required(true));
    let matches = cmd.get_matches();
    let fin = matches.get_one::<String>("input").expect("input file is required");

    let result = rhino::vm::execute_main_module(fin.as_ref()).unwrap();
    match result {
        Some(x) => println!("{:?}", x),
        None => tracing::error!("Error running module {}", fin),
    }
    // FIXME: repl doesn't work properly
}
