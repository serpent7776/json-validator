{
  open Parser
}

let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let nonzero = ['1'-'9']
let digit = ['0'-'9']
let frac = '.' digit+
let exp = ['e' 'E'] ['+' '-']? digit+
let int0 = '0' | nonzero digit*

rule token = parse
  | [' ' '\t' '\n' '\r']+   { token lexbuf }
  | '"'                     { astring lexbuf; STRING }
  | '{'                     { LBRACE }
  | '}'                     { RBRACE }
  | '['                     { LBRACKET }
  | ']'                     { RBRACKET }
  | ':'                     { COLON }
  | ','                     { COMMA }
  | '-'? int0 frac? exp?    { NUMBER }
  | "true"                  { BOOL }
  | "false"                 { BOOL }
  | "null"                  { NULL }
  | eof                     { EOF }
  | _ as c                  { failwith (Printf.sprintf "unexpected character: %C" c) }

and astring = parse
  | [^ '"' '\\']+ { astring lexbuf }
  | '"'           { () }
  | '\\' '"'      { astring lexbuf }
  | '\\' '\\'     { astring lexbuf }
  | '\\' '/'      { astring lexbuf }
  | '\\' 'b'      { astring lexbuf }
  | '\\' 'f'      { astring lexbuf }
  | '\\' 'n'      { astring lexbuf }
  | '\\' 'r'      { astring lexbuf }
  | '\\' 't'      { astring lexbuf }
  | '\\' 'u' hex hex hex hex { astring lexbuf }
  | eof           { failwith "EOF" }
