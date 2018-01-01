{
open Parser
open Syntax
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
| "="
 {EQUAL }
| "<"
 { LESS }
| ">"
 { GREATER }
| "("
{ LPAREN }
| ")"
{ RPAREN }
| "Int"
 { INT }
| "Bool"
 { BOOL }
| "->"
 { ALLOW }
| ":"
 { COLON }
| "??"
 { QUESTION }
|eof
 { EOF }
| lower (digit|lower|upper|'_')* as id
 { ID id }
| upper (digit|lower|upper|'_')* as id
 { CAPID id } 