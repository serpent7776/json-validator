use lalrpop_util::lalrpop_mod;
use std::env;
use std::fs;

lalrpop_mod!(pub json);

fn main() {
    let args = env::args().collect::<Vec<String>>();
    let contents = fs::read_to_string(&args[1]).expect("cannot read file");
    json::jsonParser::new().parse(&contents).unwrap();
}
