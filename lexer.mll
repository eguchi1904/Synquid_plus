{
open Parser

}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule main = parse

| space+
 { main lexbuf }
| "\n"
    { Lexing.new_line lexbuf;NEWLINE}     
| "data"
 { DATA }
| "where"
 { WHERE }
| "measure"
 { MEASURE }
| "termination"
 { TERMINATION }


| "="
 {EQUAL }
| "!="
 { NEQUAL }
| "!"
 { NOT }
| "&&"
 { AND }
| "||"
 { OR }
| "==>"
 { IMPLIES }
| "<==>"
 { IFF }
| "<"
 { LESS }
| "<="
 { LESS_EQUAL } 
| ">"
 { GREATER }
| ">="
 { GREATER_EQUAL } 
| '-'
    { MINUS }
| '+' 
    { PLUS }
| '*'
    { AST }
| "in"
 { IN }
| "if"
 { IF }
| "then"
 { THEN }
| "else"
 { ELSE }
    
| "Int"
 { INTSYMBOL }
| "Bool"
 { BOOLSYMBOL }
| "Set"
 {SET }
| "->"
 { ALLOW }
| ":"
 { COLON }
| "??"
 { QUESTION }
| "("
 { LPAREN }
| ")"
 { RPAREN }
| "["
 { LSQBRAC }
| "]"
 { RSQBRAC }
| "{"
 { LCURBRAC }
| "}"
 { RCURBRAC }
| "|"
 { PIPE }
| '.'
 { DOT }
| ','
 { COMMA } 

| "_v"
 { VALVAR }
| "True"
 { TRUE }
| "False"
 { FALSE }
| digit+ as n
 { INT (int_of_string n) }
|eof
 { EOF }
| (lower|'_') (digit|lower|upper|'_')* as id
 { ID id }
| upper (digit|lower|upper|'_')* as id
 { CAPID id }
| _
    { failwith
	(Printf.sprintf "unknown token %s near line %d characters %d-%d"
	   (Lexing.lexeme lexbuf)
	   ((Lexing.lexeme_start_p lexbuf).Lexing.pos_lnum)
	   (Lexing.lexeme_start lexbuf)
	   (Lexing.lexeme_end lexbuf)) }