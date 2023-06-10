use std::io::Read;

use json_validator::validate_bytes;

fn main() {
    match validate_bytes(std::io::stdin().bytes()) {
        Ok(()) => println!("Ok"),
        Err((err, pos)) => println!("Error {} at {}", err, pos),
    }
}
