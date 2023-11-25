open Lexing

let parse_with_error lexbuf =
  try Parser.json Lexer.token lexbuf with
  | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      Printf.eprintf "Syntax error at line %d, position %d\n" pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1);
      exit (-1)
  | Failure msg ->
      let pos = lexbuf.lex_curr_p in
      Printf.eprintf "Failure %s at line %d, position %d\n" msg pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1);
      exit (-1)

let main () =
  let lexbuf = Lexing.from_channel stdin in
  parse_with_error lexbuf

let () = main ()
