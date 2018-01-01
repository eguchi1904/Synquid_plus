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

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"

open Syntax

# 26 "parser.ml"
let yytransl_const = [|
  257 (* DATA *);
  258 (* WHERE *);
  261 (* EQUAL *);
  262 (* LESS *);
  263 (* GREATER *);
  264 (* LPAREN *);
  265 (* RPAREN *);
  266 (* INT *);
  267 (* BOOL *);
  268 (* ALLOW *);
  269 (* COLON *);
  270 (* QUESTION *);
    0 (* EOF *);
  271 (* NEWLINE *);
    0|]

let yytransl_block = [|
  259 (* ID *);
  260 (* CAPID *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\002\000\006\000\003\000\
\003\000\004\000\005\000\007\000\007\000\007\000\009\000\009\000\
\009\000\009\000\010\000\010\000\008\000\008\000\000\000"

let yylen = "\002\000\
\002\000\002\000\002\000\001\000\001\000\005\000\003\000\002\000\
\001\000\005\000\005\000\005\000\002\000\001\000\001\000\001\000\
\001\000\003\000\002\000\001\000\002\000\000\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\005\000\000\000\000\000\004\000\023\000\000\000\
\000\000\000\000\000\000\000\000\000\000\001\000\002\000\003\000\
\000\000\007\000\000\000\000\000\000\000\000\000\000\000\015\000\
\016\000\000\000\000\000\021\000\000\000\006\000\000\000\017\000\
\000\000\013\000\000\000\011\000\000\000\000\000\008\000\019\000\
\018\000\000\000\000\000\000\000\000\000\012\000\010\000"

let yydgoto = "\002\000\
\007\000\008\000\030\000\031\000\009\000\010\000\026\000\021\000\
\027\000\034\000"

let yysindex = "\003\000\
\024\000\000\000\000\000\007\255\253\254\000\000\000\000\024\000\
\024\000\024\000\010\255\013\255\008\255\000\000\000\000\000\000\
\019\255\000\000\005\255\019\255\032\255\009\255\005\255\000\000\
\000\000\019\255\019\255\000\000\024\255\000\000\032\255\000\000\
\022\255\000\000\014\255\000\000\028\255\030\255\000\000\000\000\
\000\000\019\255\005\255\005\255\019\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\045\255\000\000\000\000\018\000\000\000\001\000\000\000\000\000\
\000\000\044\000\031\000\000\000\000\000\000\000\048\000\000\000\
\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\031\255\000\000\000\000\038\000\000\000\000\000"

let yygindex = "\000\000\
\037\000\000\000\019\000\000\000\000\000\000\000\241\255\236\255\
\237\255\020\000"

let yytablesize = 307
let yytable = "\028\000\
\017\000\012\000\033\000\001\000\020\000\036\000\037\000\035\000\
\022\000\013\000\011\000\017\000\023\000\033\000\024\000\025\000\
\023\000\022\000\024\000\025\000\019\000\044\000\041\000\006\000\
\047\000\032\000\018\000\045\000\046\000\023\000\014\000\024\000\
\025\000\020\000\022\000\029\000\038\000\022\000\022\000\042\000\
\022\000\022\000\043\000\022\000\014\000\015\000\016\000\009\000\
\022\000\039\000\000\000\000\000\040\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\017\000\017\000\000\000\017\000\020\000\020\000\000\000\020\000\
\000\000\017\000\000\000\000\000\017\000\020\000\000\000\017\000\
\000\000\022\000\022\000\020\000\022\000\022\000\000\000\003\000\
\004\000\022\000\005\000\022\000\022\000\022\000\014\000\014\000\
\000\000\014\000\014\000\000\000\000\000\022\000\022\000\014\000\
\022\000\022\000\022\000\022\000\022\000\000\000\022\000\009\000\
\009\000\000\000\009\000"

let yycheck = "\020\000\
\000\000\005\001\022\000\001\000\000\000\026\000\027\000\023\000\
\004\001\013\001\004\001\002\001\008\001\033\000\010\001\011\001\
\008\001\000\000\010\001\011\001\013\001\042\000\009\001\000\000\
\045\000\004\001\014\001\043\000\044\000\008\001\000\000\010\001\
\011\001\015\001\004\001\004\001\013\001\000\000\008\001\012\001\
\010\001\011\001\013\001\000\000\008\000\009\000\010\000\000\000\
\004\001\031\000\255\255\255\255\033\000\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\000\001\001\001\255\255\003\001\000\001\001\001\255\255\003\001\
\255\255\009\001\255\255\255\255\012\001\009\001\255\255\015\001\
\255\255\000\001\001\001\015\001\003\001\004\001\255\255\000\001\
\001\001\008\001\003\001\010\001\011\001\012\001\000\001\001\001\
\255\255\003\001\004\001\255\255\255\255\000\001\001\001\009\001\
\003\001\004\001\012\001\000\001\001\001\255\255\003\001\000\001\
\001\001\255\255\003\001"

let yynames_const = "\
  DATA\000\
  WHERE\000\
  EQUAL\000\
  LESS\000\
  GREATER\000\
  LPAREN\000\
  RPAREN\000\
  INT\000\
  BOOL\000\
  ALLOW\000\
  COLON\000\
  QUESTION\000\
  EOF\000\
  NEWLINE\000\
  "

let yynames_block = "\
  ID\000\
  CAPID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.env) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.env * Syntax.env * (string list) ) in
    Obj.repr(
# 43 "parser.mly"
 ( match (_2) with
   (env,fundecs,l) -> (_1@env, fundecs, l)
   )
# 206 "parser.ml"
               : Syntax.env * Syntax.env * (string list) ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string * Syntax.ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.env * Syntax.env * (string list) ) in
    Obj.repr(
# 47 "parser.mly"
 ( match _2 with
   (env,fundecs,l) -> (env, _1::fundecs, l)
   )
# 216 "parser.ml"
               : Syntax.env * Syntax.env * (string list) ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.env * Syntax.env * (string list) ) in
    Obj.repr(
# 51 "parser.mly"
 ( match _2 with
   (env,fundecs,l) -> (env, fundecs, _1::l)
 )
# 226 "parser.ml"
               : Syntax.env * Syntax.env * (string list) ))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
    ( ([],[],[]))
# 232 "parser.ml"
               : Syntax.env * Syntax.env * (string list) ))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
    ( failwith
     (let line_pos=(Parsing.symbol_start_pos ()).Lexing.pos_bol in
	(Printf.sprintf "parse error near line %d charactfers %d-%d"
	   ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
	   ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-line_pos)
	   ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-line_pos))) )
# 243 "parser.ml"
               : Syntax.env * Syntax.env * (string list) ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'nl) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Syntax.env) in
    Obj.repr(
# 66 "parser.mly"
                                ( _5 )
# 252 "parser.ml"
               : Syntax.env))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 69 "parser.mly"
                    (_1)
# 259 "parser.ml"
               : string))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string * Syntax.ty) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Syntax.env) in
    Obj.repr(
# 72 "parser.mly"
                      (_1 :: _2)
# 267 "parser.ml"
               : Syntax.env))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string * Syntax.ty) in
    Obj.repr(
# 73 "parser.mly"
           ([_1])
# 274 "parser.ml"
               : Syntax.env))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Syntax.ty) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'nl) in
    Obj.repr(
# 76 "parser.mly"
                             ((_1,_4))
# 283 "parser.ml"
               : string * Syntax.ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Syntax.ty) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'nl) in
    Obj.repr(
# 79 "parser.mly"
                         ((_1,_4))
# 292 "parser.ml"
               : string * Syntax.ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'tatom) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'nl) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'nl) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Syntax.ty) in
    Obj.repr(
# 82 "parser.mly"
                        (TFun (_1,_5))
# 302 "parser.ml"
               : Syntax.ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'tatoms) in
    Obj.repr(
# 83 "parser.mly"
              ( Data(_1, _2) )
# 310 "parser.ml"
               : Syntax.ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tatom) in
    Obj.repr(
# 84 "parser.mly"
       (_1)
# 317 "parser.ml"
               : Syntax.ty))
; (fun __caml_parser_env ->
    Obj.repr(
# 87 "parser.mly"
      (Int)
# 323 "parser.ml"
               : 'tatom))
; (fun __caml_parser_env ->
    Obj.repr(
# 88 "parser.mly"
       (Bool)
# 329 "parser.ml"
               : 'tatom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 89 "parser.mly"
        ( Data(_1, []) )
# 336 "parser.ml"
               : 'tatom))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.ty) in
    Obj.repr(
# 90 "parser.mly"
                     ( _2 )
# 343 "parser.ml"
               : 'tatom))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'tatom) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'tatoms) in
    Obj.repr(
# 94 "parser.mly"
               ( _1 :: _2 )
# 351 "parser.ml"
               : 'tatoms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tatom) in
    Obj.repr(
# 95 "parser.mly"
        ( [ _1 ] )
# 358 "parser.ml"
               : 'tatoms))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'nl) in
    Obj.repr(
# 98 "parser.mly"
             (())
# 365 "parser.ml"
               : 'nl))
; (fun __caml_parser_env ->
    Obj.repr(
# 99 "parser.mly"
  ( () )
# 371 "parser.ml"
               : 'nl))
(* Entry toplevel *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let toplevel (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.env * Syntax.env * (string list) )
