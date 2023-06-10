use std::io::Read;

use json_validator::validate_bytes;

fn main() {
    let _ = validate_bytes(std::io::stdin().bytes());
}
