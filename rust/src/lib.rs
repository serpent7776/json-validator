use std::io::Read;

use unicode_reader::CodePoints;

#[derive(Clone)]
pub struct Position {
    line: usize,
    col: usize,
    byte: usize,
}

impl Position {
    fn new() -> Position {
        Position{line: 1, col: 1, byte: 1}
    }
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
    Garbage,
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
            Error::Garbage => write!(fmt, "Trailing characters at the end of the string"),
        }
    }
}

struct Chars<R: std::io::Read> {
    iter: std::iter::Peekable<CodePoints<std::io::Bytes<R>>>,
    pos: Position,
}

impl<R: std::io::Read> Iterator for Chars<R> {
    type Item = <std::iter::Peekable<CodePoints<std::io::Bytes<R>>> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.iter.next();
        match &next {
            Some(Ok('\n')) => {
                self.pos.line += 1;
                self.pos.col = 0;
            },
            _ => {},
        }
        self.pos.byte += 1;
        self.pos.col += 1;
        next
    }
}

impl<R: std::io::Read> Chars<R> {
    fn from_bytes(bytes: std::io::Bytes<R>) -> Chars<R> {
        Chars {iter: CodePoints::from(bytes).peekable(), pos: Position::new()}
    }
    fn from_str(s: &str) -> Chars<&[u8]> {
        Chars {iter: CodePoints::from(<str as AsRef<[u8]>>::as_ref(s).bytes()).peekable(), pos: Position::new()}
    }

    fn peek(&mut self) -> Option<&<std::iter::Peekable<CodePoints<std::io::Bytes<R>>> as Iterator>::Item> {
        self.iter.peek()
    }
}

type ValidationResult = Result<(), (Error, Position)>;
type ValidationPart<R> = Result<Chars<R>, (Error, Position, Chars<R>)>;

fn advance<I: Iterator>(mut iter: I) -> I {
    iter.next();
    iter
}

fn io_error(e: &std::io::Error) -> Error {
    Error::IoError(e.to_string())
}

fn validate<R: std::io::Read>(chars: Chars<R>) -> ValidationResult {
    let mut chars = skip_ws(chars);
    if let None = chars.peek() {return Err((Error::EmptyString, chars.pos));}
    match validate_value(chars) {
        Err((e, p, _)) => Err((e, p)),
        Ok(chars) => {
            let mut chars = skip_ws(chars);
            match chars.peek() {
                None => Ok(()),
                Some(Ok(_)) => Err((Error::Garbage, chars.pos.clone())),
                Some(Err(e)) => Err((io_error(e), chars.pos.clone())),
            }
        },
    }
}

pub fn validate_bytes<R: std::io::Read>(bytes: std::io::Bytes<R>) -> ValidationResult {
    validate(Chars::from_bytes(bytes))
}

pub fn validate_str(s: &str) -> ValidationResult {
    validate(Chars::<&[u8]>::from_str(s))
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
    skip(chars, char::is_whitespace)
}

fn validate_with<R: std::io::Read, F: FnOnce(Chars<R>, char) -> ValidationPart<R>>(mut chars: Chars<R>, f: F) -> ValidationPart<R> {
    match chars.peek() {
        None => Err((Error::OutOfBounds, chars.pos.clone(), chars)),
        Some(Err(e)) => Err((io_error(e), chars.pos.clone(), chars)),
        Some(Ok(c)) => {
            let x = *c;
            f(chars, x)
        }
    }
}

fn validate_char<R: std::io::Read>(chars: Chars<R>, ch: char) -> ValidationPart<R> {
    validate_with(chars, |chars: Chars<R>, c: char|
        if c == ch {Ok(advance(chars))}
        else {Err((Error::CharMismatch{expected: ch, actual: c}, chars.pos.clone(), chars))})
}

fn validate_escaped_char<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    let escaped = ['"', '\\', 'r', 'n', 't', '\u{0008}', '\u{000C}'];
    validate_with(chars, |chars: Chars<R>, c: char|
        if escaped.contains(&c) {Ok(advance(chars))}
        else {Err((Error::CharOutside{expected: escaped.into(), actual: c}, chars.pos.clone(), chars))})
}

fn validate_hex<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    fn is_hex(ch: char) -> bool {
        ('0'..='9').contains(&ch) || ('a'..='f').contains(&ch) || ('A'..='F').contains(&ch)
    }

    validate_with(chars, |chars: Chars<R>, c: char|
        if is_hex(c) {Ok(advance(chars))}
        else {Err((Error::HexCharNeeded, chars.pos.clone(), chars))})
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
        else {Err((Error::DigitsNeeded, chars.pos.clone(), chars))})?;
    let chars = skip(chars, is_digit);
    Ok(chars)
}

fn validate_value<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    let mut chars = skip_ws(chars);
    match chars.peek() {
        Some(Ok('0'..='9')) => validate_number(chars),
        Some(Ok('-')) => validate_number(advance(chars)),
        Some(Ok('"')) => {
            let chars = validate_string_contents(advance(chars))?;
            validate_char(chars, '"')
        },
        Some(Ok('[')) => {
            let chars = skip_ws(advance(chars));
            let chars = validate_array_elements(chars)?;
            validate_char(skip_ws(chars), ']')
        },
        Some(Ok('{')) => {
            let chars = skip_ws(advance(chars));
            let chars = validate_object_pairs(chars)?;
            validate_char(skip_ws(chars), '}')
        },
        Some(Ok(c)) => {
            if c.is_alphabetic() {validate_literal(chars)}
            else {Err((Error::InvalidValue, chars.pos.clone(), chars))}
        },
        Some(Err(e)) => Err((io_error(&e), chars.pos.clone(), chars)),
        None => Err((Error::OutOfBounds, chars.pos.clone(), chars)),
    }
}

fn validate_number<R: std::io::Read>(chars: Chars<R>) -> ValidationPart<R> {
    let mut chars = validate_number_integer_part(chars)?;
    match chars.peek() {
        None => Ok(chars),
        Some(Err(e)) => Err((io_error(e), chars.pos.clone(), chars)),
        Some(Ok('.')) => {
            let mut chars = validate_number_fraction_part(advance(chars))?;
            match chars.peek() {
                None => Ok(chars),
                Some(Err(e)) => Err((io_error(e), chars.pos.clone(), chars)),
                Some(Ok('e')) => {
                    let chars = validate_plus_or_minus(advance(chars))?;
                    Ok(validate_number_exponent_part(chars)?)
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

    let chars = skip(chars, is_plus_or_minus);
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
            None => return Err((Error::OutOfBounds, chars.pos.clone(), chars)),
            Some(Err(e)) => return Err((io_error(e), chars.pos.clone(), chars)),
            Some(Ok('"')) => return Ok(chars),
            Some(Ok('\\')) => {
                chars = advance(chars);
                match chars.peek() {
                    None => return Err((Error::OutOfBounds, chars.pos.clone(), chars)),
                    Some(Err(e)) => return Err((io_error(e), chars.pos.clone(), chars)),
                    Some(Ok('u')) => {
                        chars = advance(chars);
                        chars = validate_hex(chars)?;
                        chars = validate_hex(chars)?;
                        chars = validate_hex(chars)?;
                        chars = validate_hex(chars)?;
                    },
                    Some(Ok(_)) => chars = validate_escaped_char(chars)?,
                }
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
        match validate_char(skip_ws(chars), ',') {
            Ok(c) => {chars = skip_ws(c)},
            Err((_, _, c)) => {return Ok(c)},
        }
    }
}

fn validate_object_pairs<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    if let Some(Ok('}')) = chars.peek() {return Ok(chars);}
    loop {
        chars = validate_string(chars)?;
        chars = validate_char(skip_ws(chars), ':')?;
        chars = validate_value(chars)?;
        match validate_char(skip_ws(chars), ',') {
            Ok(c) => {chars = skip_ws(c)},
            Err((_, _, c)) => {return Ok(c)},
        }
    }
}

fn validate_chars<R: std::io::Read>(mut chars: Chars<R>, s: &str) -> ValidationPart<R> {
    let mut s = s.chars();
    loop {
        match s.next() {
            None => {
                match chars.peek() {
                    None => return Ok(chars),
                    Some(Err(e)) => return Err((io_error(&e), chars.pos.clone(), chars)),
                    Some(Ok(ch)) => {
                        if ch.is_alphabetic() {return Err((Error::UnrecognisedLiteral, chars.pos.clone(), chars))}
                        else {return Ok(chars)}
                    },
                }
            },
            Some(s) => {
                match chars.next() {
                    None => return Err((Error::CharMissing(s), chars.pos.clone(), chars)),
                    Some(Err(e)) => return Err((io_error(&e), chars.pos.clone(), chars)),
                    Some(Ok(ch)) =>
                        if ch != s {
                            return Err((Error::CharMismatch{expected: s, actual: ch}, chars.pos.clone(), chars))
                        },
                }
            },
        }
    }
}

fn validate_literal<R: std::io::Read>(mut chars: Chars<R>) -> ValidationPart<R> {
    match chars.next() {
        None => return Err((Error::OutOfBounds, chars.pos.clone(), chars)),
        Some(Ok('n')) => validate_chars(chars, "ull"),
        Some(Ok('t')) => validate_chars(chars, "rue"),
        Some(Ok('f')) => validate_chars(chars, "alse"),
        Some(Ok(_)) => Err((Error::UnrecognisedLiteral, chars.pos.clone(), chars)),
        Some(Err(e)) => Err((io_error(&e), chars.pos.clone(), chars)),
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
            Ok(()) => assert!(
                false,
                "\n\tFailed for {}: Expected to fail with {}, but succeeded",
                arg, expected_err
            ),
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

    // numbers
    ok!(validate_str, "42", number_parses_ok);
    ok!(validate_str, "0", zero_parses_ok);
    ok!(validate_str, "-1", negative_parses_ok);
    ok!(validate_str, "1.23", float_parses_ok);
    ok!(validate_str, "1.230", float_with_trailing_zero_parses_ok);
    fails!(validate_str, "1.", Error::OutOfBounds, float_without_fraction_fails_to_parse);
    fails!(validate_str, "0.", Error::OutOfBounds, zero_without_fraction_fails_to_parse);
    fails!(validate_str, "-0.", Error::OutOfBounds, negative_zero_without_fraction_fails_to_parse);
    ok!(validate_str, "6.999e3", float_with_exponent_parses_ok);
    ok!(validate_str, "-1.2e9", negative_float_with_exponent_parses_ok);
    fails!(validate_str, "6.999e", Error::OutOfBounds, float_without_exponent_fails_to_parse);
    fails!(validate_str, "1.e1", Error::DigitsNeeded, float_with_dot_and_exponent_but_without_fraction_fails_to_parse);
    ok!(validate_str, "1e1", float_with_exponent_but_without_fraction_parses_ok);
    ok!(validate_str, "1e-1", float_with_negative_exponent_parses_ok);
    ok!(validate_str, "1.0e-1", float_with_fraction_part_and_negative_exponent_parses_ok);
    fails!(validate_str, "1.0e-", Error::OutOfBounds, float_with_exponent_minus_but_without_digits_fails_to_parse);
    fails!(validate_str, "1.x", Error::DigitsNeeded, float_with_invalid_fraction_fails_to_parse);
    fails!(validate_str, "-1.y", Error::DigitsNeeded, negative_float_with_invalid_fraction_fails_to_parse);
    fails!(validate_str, ".12", Error::InvalidValue, float_without_integer_part_fails_to_parse);
    fails!(validate_str, "-.12", Error::DigitsNeeded, negative_float_without_integer_part_fails_to_parse);

    // strings
    ok!(validate_str, r#""""#, empty_string_parses_ok);
    fails!(validate_str, r#"""#, Error::OutOfBounds, missing_ending_quote_in_empty_string);
    ok!(validate_str, r#""foobar""#, nonempty_string_parses_ok);
    ok!(validate_str, r#""a\nb""#, string_with_newline_parses_ok);
    ok!(validate_str, r#""foo\\bar""#, string_with_escaped_backslash_parses_ok);
    ok!(validate_str, r#""foo bar""#, string_with_space_parses_ok);
    ok!(validate_str, r#""foo/bar""#, string_with_slash_parses_ok);
    fails!(validate_str, r#""foobar"#, Error::OutOfBounds, missing_ending_quote_in_nonempty_string);
    fails!(validate_str, r#""foo"bar"#, Error::Garbage, extra_letters_after_string);
    fails!(validate_str, r#""foo\"bar"#, Error::OutOfBounds, missing_ending_quote_with_inner_escaped_quote);
    ok!(validate_str, r#""a b c""#, string_with_inner_spaces_parses_ok);
    ok!(validate_str, r#"" a b c ""#, string_with_leading_trailing_spaces_parses_ok);
    ok!(validate_str, r#""foo\"bar""#, string_with_escaped_quote_parses_ok);
    ok!(validate_str, r#""\u1234""#, unicode_symbol_parses_ok);
    ok!(validate_str, r#""\u1234\uabcd""#, string_with_two_unicode_symbols_parses_ok);
    ok!(validate_str, r#""\u1234\uabcd\u00Ff""#, string_with_three_unicode_symbols_parses_ok);
    ok!(validate_str, r#""foo\u12cdbar""#, string_with_inner_unicode_symbol_parses_ok);
    fails!(validate_str, r#""\u12cx""#, Error::HexCharNeeded, invalid_unicode_sequence);
    fails!(validate_str, r#""\"#, Error::OutOfBounds, missing_ending_quote_with_escaped_quote);
    fails!(validate_str, r#""\x""#, Error::CharOutside{expected: vec!['"', '\\', 'r', 'n', 't', '\u{8}', '\u{c}'], actual: 'x'}, invalid_escape_sequence);

    // arrays
    ok!(validate_str, "[]", empty_array_parses_ok);
    ok!(validate_str, "[null]", array_with_null_parses_ok);
    ok!(validate_str, "[[null]]", nested_array_with_null_parses_ok);
    ok!(validate_str, "[true]", array_with_true_parses_ok);
    ok!(validate_str, "[false]", array_with_false_parses_ok);
    ok!(validate_str, "[true,false]", array_with_true_and_false_parses_ok);
    ok!(validate_str, "[1.2]", array_with_single_number_parses_ok);
    ok!(validate_str, r#"["abc"]"#, array_with_string_parses_ok);
    ok!(validate_str, "[[[]]]", deeply_nested_empty_array_parses_ok);
    ok!(validate_str, "[[[\"a\"]]]", deeply_nested_array_with_string_parses_ok);
    fails!(validate_str, "[", Error::OutOfBounds, sole_opening_bracket_fails_to_parse_as_array);
    fails!(validate_str, "]", Error::InvalidValue, sole_closing_bracket_fails_to_parse_as_array);
    fails!(validate_str, "[[[", Error::OutOfBounds, multiple_opening_brackets_fail_to_parse_as_array);
    fails!(validate_str, "]]]", Error::InvalidValue, multiple_closing_brackets_fail_to_parse_as_array);
    ok!(validate_str, "[1,2,3]", array_with_numbers_parses_ok);
    fails!(validate_str, r#"[""#, Error::OutOfBounds, unclosed_string_in_unclosed_array_fail_to_parse);
    ok!(validate_str, "[true,false,null,0]", array_with_different_types_parses_ok);
    ok!(validate_str, "[[],[]]", nested_array_parses_ok);
    fails!(validate_str, "[1,", Error::OutOfBounds, missing_closing_bracket_after_first_element);
    fails!(validate_str, "[1,]", Error::InvalidValue, missing_second_element_in_array);
    fails!(validate_str, "[1,2,]", Error::InvalidValue, missing_third_element_in_array);
    fails!(validate_str, "[1,2,", Error::OutOfBounds, missing_closing_bracket_after_second_element);

    // objects
    ok!(validate_str, "{}", empty_object_parses_ok);
    ok!(validate_str, r#"{"1":1}"#, object_with_single_key_value_pair_parses_ok);
    ok!(validate_str, r#"{"foo":"bar"}"#, object_with_string_value_parses_ok);
    ok!(validate_str, r#"{"":""}"#, object_with_empty_key_parses_ok);
    ok!(validate_str, r#"{"12":[]}"#, object_with_empty_array_value_parses_ok);
    ok!(validate_str, r#"{"a":1,"b":2,"c":3}"#, object_with_many_integer_values_parses_ok);
    ok!(validate_str, r#"{"x":9.8e7}"#, object_with_float_number_value_parses_ok);
    fails!(validate_str, r#"{"1":1"#, Error::OutOfBounds, missing_closing_paren);
    fails!(validate_str, r#"{"foo"}"#, Error::CharMismatch{expected: ':', actual: '}'}, missing_colon_and_value_after_key);
    fails!(validate_str, r#"{"foo":}"#, Error::InvalidValue, missing_value_after_key);

    // values with spaces
    fails!(validate_str, "   ", Error::EmptyString, just_spaces_fail_to_parse);
    fails!(validate_str, " [  ", Error::OutOfBounds, missing_closing_bracket_with_spaces);
    fails!(validate_str, " ]  ", Error::InvalidValue, missing_opening_bracket_with_spaces);
    ok!(validate_str, "   null   ", null_with_spaces_parses_ok);
    ok!(validate_str, "   true   ", true_with_spaces_parses_ok);
    ok!(validate_str, "  false  ", false_with_spaces_parses_ok);
    ok!(validate_str, r#"" \u1234 \uabcd \u00Ff ""#, string_with_unicodes_with_spaces_parses_ok);
    ok!(validate_str, " [ true, false, null ] ", array_with_spaces_parses_ok);
    ok!(validate_str, " [ true , false , null ] ", array_with_more_spaces_parses_ok);
    ok!(validate_str, r#" { "a" : true , "b" : false , "c" : null } "#, object_with_spaces_parses_ok);
    ok!(validate_str, r#" {  } "#, empty_object_with_spaces_parses_ok);
    ok!(validate_str, r#" [  ] "#, empty_array_with_spaces_parses_ok);

}
