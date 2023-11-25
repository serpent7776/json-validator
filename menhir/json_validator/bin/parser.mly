%token NULL
%token BOOL
%token NUMBER
%token STRING
%token LBRACE RBRACE LBRACKET RBRACKET COLON COMMA
%token EOF

%start <unit> json

%%

json:
  | value EOF { () }

value:
  | object_value  { () }
  | array_value   { () }
  | STRING        { () }
  | NUMBER        { () }
  | NULL          { () }
  | BOOL          { () }

object_value:
  | LBRACE members? RBRACE { () }

members:
  | key_value            { () }
  | key_value COMMA members { () }

key_value:
  | STRING COLON value { () }

array_value:
  | LBRACKET elements? RBRACKET { () }

elements:
  | value            { () }
  | value COMMA elements { () }
