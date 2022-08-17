extern crate clap;
use clap::Parser;

#[derive(Debug, Parser)]
struct CliArgs {
    #[clap(short = 'i', long, forbid_empty_values = true)]
    input: String
}

fn main() {
    tracing_subscriber::fmt::init();

    let fin = CliArgs::parse().input;

    let result = rhino::vm::execute_main_module(fin.as_ref()).unwrap();
    match result {
        Some(x) => println!("{:?}", x),
        None => tracing::error!("Error running module {}", fin),
    }
    // FIXME: repl doesn't work properly
}
