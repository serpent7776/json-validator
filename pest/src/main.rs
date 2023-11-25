// use clap;
use pest::Parser;
// use pest_derive::Parser;

use std::env;
use std::fs;

#[derive(pest_derive::Parser)]
#[grammar = "json.pest"]
struct Json;

fn usage() {
    print!("JSON validator\n\nUsage: json-validate [FILE]\n\nIf FILE is provided, read and validate JSON from that file.\nOtherwise read and validate JSON from stdin.\n");
}

fn main() {
    let args = env::args().collect::<Vec<String>>();
    if args.len() > 1 {
        if args[1] == "-h" || args[1] == "--help" {
            usage();
        }
        else {
            read_from_file(&args[1]);
        }
    }
    else {
        read_from_stdin();
    }
}

fn read_from_stdin() {

}

fn read_from_file(filename: &str) {
    let contents = fs::read_to_string(filename).expect("cannot read file");
    let json = Json::parse(Rule::json, &contents);
    match json {
        Ok(_) => (),
        Err(pest::error::Error {variant, location, line_col, ..}) => {
            fail(variant, location, line_col);
        },
    };
    // assert!(json.next().is_err());
}

fn fail<R: std::fmt::Debug>(variant: pest::error::ErrorVariant<R>, location: pest::error::InputLocation, line_col: pest::error::LineColLocation) {
    print!("v={:?}, l={:?}, c={:?}\n", variant, location, line_col);
}
