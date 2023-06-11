use std::io::Read;

use unicode_reader::CodePoints;

pub struct Position {
    line: usize,
    col: usize,
    byte: usize,
}

impl std::fmt::Display for Position {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, ":{}:{} ({} byte)", self.line, self.col, self.byte)
    }
}

#[derive(PartialEq)]
pub enum Error {
    Unknown,
    EmptyString,
    IoError(String),
    CharMissing(char),
    CharMismatch{expected: char, actual: char},
    CharOutside{expected: Vec<char>, actual: char},
    DigitsNeeded,
    HexCharNeeded,
    UnrecognisedLiteral,
    InvalidValue,
    OutOfBounds,
}

impl std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Unknown => write!(fmt, "Unknown error"),
            Error::EmptyString => write!(fmt, "Empty input string"),
            Error::IoError(s) => write!(fmt, "IO error: {}", s),
            Error::CharMissing(c) => write!(fmt, "char expected: {}", c),
            Error::CharMismatch{expected, actual} => write!(fmt, "{} expected, but {} found", expected, actual),
            Error::CharOutside{expected, actual} => write!(fmt, "One of {:?} expected, but {} found", expected, actual),
            Error::DigitsNeeded => write!(fmt, "Digit expected"),
            Error::HexCharNeeded => write!(fmt, "Hex char expected"),
            Error::UnrecognisedLiteral => write!(fmt, "Unrecognised literal found"),
            Error::InvalidValue => write!(fmt, "Invalid value found"),
            Error::OutOfBounds => write!(fmt, "Unexpected end of input string"),
        }
    }
}

type Chars<R> = std::iter::Peekable<CodePoints<std::io::Bytes<R>>>;

type ValidationResult = Result<(), (Error, Position)>;
type ValidationPart<R> = Result<Chars<R>, (Error, Position, Chars<R>)>;

fn advance<I: Iterator>(mut iter: I) -> I {
    iter.next();
    iter
}

fn io_error(e: &std::io::Error) -> Error {
    Error::IoError(e.to_string())
}

fn validate<R: std::io::Read>(mut chars: Chars<R>) -> ValidationResult {
    if let None = chars.peek() {return Err((Error::EmptyString, Position{line:0, col:0, byte:0}));}
    match validate_value(chars) {
        Ok(_) => Ok(()),
        Err((e, p, _)) => Err((e, p)),
    }
}

pub fn validate_bytes<R: std::io::Read>(bytes: std::io::Bytes<R>) -> ValidationResult {
    validate(CodePoints::from(bytes).peekable())
}

pub fn validate_str(s: &str) -> ValidationResult {
    validate(CodePoints::from(<str as AsRef<[u8]>>::as_ref(s).bytes()).peekable())
}

fn skip<R: std::io::Read, F: Fn(char) -> bool>(mut chars: Chars<R>, f: F) -> Chars<R> {
    loop {
        match chars.peek() {
            Some(Ok(ch)) => {
                if !f(*ch) { return chars; }
                else { chars.next() };
            }
            _ => return chars,
        }
    }
}

fn skip_ws<R: std::io::Read>(chars: Chars<R>) -> Chars<R> {
    todo!()
}

fn validate_with<R: std::io::Read, F: FnOnce(Chars<R>, char) -> ValidationPart<R>>(mut chars: Chars<R>, f: F) -> ValidationPart<R> {
    match chars.peek() {
        None => Err((Error::OutOfBounds, Position{line:0, col:0, byte:0}, chars)),
        Some(Err(e)) => Err((io_error(e), Position{line:0, col:0, byte:0}, chars)),
        Some(Ok(c)) => {
            let x = *c;
            f(chars, x)
        }
    }
}

fn validate_char<R: std::io::Read>(chars: Chars<R>, ch: char) -> ValidationPart<R> {
    validate_with(chars, |chars: Chars<R>, c: char|
        if c == ch {Ok(advance(chars))}
        else {Err((Error::CharMismatch{expected: ch, actual: c}, Position{line:0, col:0, byte:0}, chars))})
}

fn validate_escaped_char<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    let escaped = ['\"', '\\', '\r', '\n', '\t', '\u{0008}', '\u{000C}'];
    validate_with(chars, |chars: Chars<R>, c: char|
        if escaped.contains(&c) {Ok(advance(chars))}
        else {Err((Error::CharOutside{expected: escaped.into(), actual: c}, Position{line:0, col:0, byte:0}, chars))})
}

fn validate_hex<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    fn is_hex(ch: char) -> bool {
        ('0'..='9').contains(&ch) || ('a'..='f').contains(&ch) || ('A'..='F').contains(&ch)
    }

    validate_with(chars, |chars: Chars<R>, c: char|
        if is_hex(c) {Ok(advance(chars))}
        else {Err((Error::HexCharNeeded, Position{line:0, col:0, byte:0}, chars))})
}

fn validate_number_digits<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    fn is_digit(ch: char) -> bool {
        match ch {
            '0'..='9' => true,
            _ => false,
        }
    }

    let chars = validate_with(chars, |chars: Chars<R>, c: char|
        if is_digit(c) {Ok(advance(chars))}
        else {Err((Error::DigitsNeeded, Position{line:0, col:0, byte:0}, chars))})?;
    let chars = skip(chars, is_digit);
    Ok(chars)
}

fn validate_value<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    match chars.peek() {
        Some(Ok('0'..='9')) => validate_number(chars),
        Some(Ok('-')) => validate_number(advance(chars)),
        Some(Ok('"')) => {
            let chars = validate_string_contents(advance(chars))?;
            validate_char(chars, '"')
        },
        Some(Ok('[')) => {
            let chars = validate_array_elements(advance(chars))?;
            validate_char(chars, ']')
        },
        Some(Ok('{')) => {
            let chars = validate_object_pairs(advance(chars))?;
            validate_char(chars, '}')
        },
        Some(Ok(_)) => validate_literal(chars),
        Some(Err(e)) => Err((io_error(&e), Position{line:0, col:0, byte:0}, chars)),
        None => Err((Error::OutOfBounds, Position{line:0, col:0, byte:0}, chars)),
    }
}

fn validate_number<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    let mut chars = validate_number_integer_part(chars)?;
    match chars.peek() {
        None => Ok(chars),
        Some(Err(e)) => Err((io_error(e), Position{line:0, col:0, byte:0}, chars)),
        Some(Ok('.')) => {
            let mut chars = validate_number_fraction_part(advance(chars))?;
            match chars.peek() {
                None => Ok(chars),
                Some(Err(e)) => Err((io_error(e), Position{line:0, col:0, byte:0}, chars)),
                Some(Ok('e')) => {
                    let chars = validate_plus_or_minus(chars)?;
                    Ok(validate_number_exponent_part(advance(chars))?)
                },
                Some(Ok(_)) => return Ok(chars),
            }
        },
        Some(Ok('e')) => {
            let chars = validate_plus_or_minus(advance(chars))?;
            validate_number_exponent_part(chars)
        },
        Some(Ok(_)) => return Ok(chars),
    }
}

fn validate_plus_or_minus<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    fn is_plus_or_minus(ch: char) -> bool {
        match ch {
            '+' => true,
            '-' => true,
            _ => false,
        }
    }

    let chars = skip(chars, |ch: char| is_plus_or_minus(ch));
    Ok(chars)
}

fn validate_number_integer_part<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    validate_number_digits(chars)
}

fn validate_number_fraction_part<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    validate_number_digits(chars)
}

fn validate_number_exponent_part<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    validate_number_digits(chars)
}

fn validate_string_contents<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    fn unescaped(ch: char) -> bool {
        match ch {
            '"' => false,
            '\\' => false,
            _ => true,
        }
    }
    loop {
        chars = skip(chars, unescaped);
        match chars.peek() {
            None => return Err((Error::OutOfBounds, Position{line:0, col:0, byte:0}, chars)),
            Some(Err(e)) => return Err((io_error(e), Position{line:0, col:0, byte:0}, chars)),
            Some(Ok('"')) => return Ok(chars),
            Some(Ok('u')) => {
                chars = validate_hex(chars)?;
                chars = validate_hex(chars)?;
                chars = validate_hex(chars)?;
                chars = validate_hex(chars)?;
            },
            Some(Ok('\\')) => {
                chars = validate_escaped_char(chars)?;
            },
            Some(Ok(_)) => unreachable!(),
        };
    }
}

fn validate_string<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    let chars = validate_char(chars, '"')?;
    let chars = validate_string_contents(chars)?;
    validate_char(chars, '"')
}

fn validate_array_elements<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    if let Some(Ok(']')) = chars.peek() {return Ok(chars);}
    loop {
        chars = validate_value(chars)?;
        match validate_char(chars, ',') {
            Ok(c) => {chars = c},
            Err((_, _, c)) => {return Ok(c)},
        }
    }
}

fn validate_object_pairs<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    if let Some(Ok('}')) = chars.peek() {return Ok(chars);}
    loop {
        chars = validate_string(chars)?;
        chars = validate_char(chars, ':')?;
        chars = validate_value(chars)?;
        match validate_char(chars, ',') {
            Ok(c) => {chars = c},
            Err((_, _, c)) => {return Ok(c)},
        }
    }
}

fn validate_chars<R: std::io::Read>(mut chars: Chars<R>, s: &str) -> ValidationPart<R> {
    let mut s = s.chars();
    loop {
        match s.next() {
            None => return Ok(chars),
            Some(s) =>
                match chars.next() {
                    None => return Err((Error::CharMissing(s), Position{line:0, col:0, byte:0}, chars)),
                    Some(Err(e)) => return Err((io_error(&e), Position{line:0, col:0, byte:0}, chars)),
                    Some(Ok(ch)) =>
                        if ch != s {
                            return Err((Error::CharMismatch{expected: s, actual: ch}, Position{line:0, col:0, byte:0}, chars))
                        },
                },
        }
    }
}

fn validate_literal<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    match chars.next() {
        None => return Err((Error::OutOfBounds, Position{line:0, col:0, byte:0}, chars)),
        Some(Ok('n')) => validate_chars(chars, "ull"),
        Some(Ok('t')) => validate_chars(chars, "rue"),
        Some(Ok('f')) => validate_chars(chars, "alse"),
        Some(Ok(_)) => Err((Error::UnrecognisedLiteral, Position{line:0, col:0, byte:0}, chars)),
        Some(Err(e)) => Err((io_error(&e), Position{line:0, col:0, byte:0}, chars)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fails<Arg: std::fmt::Display + ?Sized, F: FnOnce(&Arg) -> ValidationResult>(f: F, arg: &Arg, expected_err: Error) {
        let actual = f(arg);
        match actual {
            Err((actual_err, _)) => assert!(
                expected_err == actual_err,
                "\n\tFailed for {}: Expected to fail with {}, but failed with {} instead",
                arg,
                expected_err,
                actual_err
            ),
            Ok(()) => {},
        }
    }

    fn ok<Arg: std::fmt::Display + ?Sized, F: FnOnce(&Arg) -> ValidationResult>(f: F, arg: &Arg) {
        let actual = f(arg);
        match actual {
            Ok(()) => {},
            Err((actual_err, _)) => assert!(
                false,
                "\n\tFailed for {}: Expected to succeed, but failed with {}",
                arg, actual_err
            ),
        }
    }

    macro_rules! fails {
        ($f: ident, $str: expr, $err: expr, $name: ident) => {
            #[test]
            fn $name() {
                fails($f, $str, $err);
            }
        };
    }

    macro_rules! ok {
        ($f: ident, $str: expr, $name: ident) => {
            #[test]
            fn $name() {
                ok($f, $str);
            }
        };
    }

    fails!(validate_str, "", Error::EmptyString, empty_string_fails_to_parse);
    fails!(validate_str, "x", Error::UnrecognisedLiteral, incorrect_value_fails);

    // literals
    ok!(validate_str, "null", null_parses_ok);
    ok!(validate_str, "true", true_parses_ok);
    ok!(validate_str, "false", false_parses_ok);
    fails!(validate_str, "truefalse", Error::UnrecognisedLiteral, unknown_ident_truefalse);

}
