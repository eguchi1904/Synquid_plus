type token =
  | DATA
  | WHERE
  | ID of (string)
  | CAPID of (string)
  | EQUAL
  | LESS
  | GREATER
  | LPAREN
  | RPAREN
  | INT
  | BOOL
  | ALLOW
  | COLON
  | QUESTION
  | EOF
  | NEWLINE

val toplevel :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Syntax.env * Syntax.env * (string list) 
