%{

open Syntax

%}


%token DATA
%token WHERE
%token <string>ID
%token <string>CAPID /*先頭が大文字のID*/

%token EQUAL
%token LESS
%token GREATER
%token LPAREN
%token RPAREN
%token INT
%token BOOL
%token ALLOW
%token COLON
%token QUESTION
%token EOF
%token NEWLINE

%nonassoc CAPID
%nonassoc COLON


%type <Syntax.env * Syntax.env * (string list) > toplevel
%type <Syntax.env> m1 /*m1によってコンストラクタの型の環境を作成*/
%type <Syntax.env> cons_decs
%type <string * Syntax.ty> cons_dec
%type <string * Syntax.ty> fun_dec
%type <string> m2
%type <Syntax.ty> texp
%start toplevel
    
%%

toplevel:
| m1 toplevel
 { match ($2) with
   (env,fundecs,l) -> ($1@env, fundecs, l)
   }
| fun_dec toplevel
 { match $2 with
   (env,fundecs,l) -> (env, $1::fundecs, l)
   }
| m2 toplevel
 { match $2 with
   (env,fundecs,l) -> (env, fundecs, $1::l)
 }
| EOF
    { ([],[],[])}

| error
    { failwith
     (let line_pos=(Parsing.symbol_start_pos ()).Lexing.pos_bol in
	(Printf.sprintf "parse error near line %d charactfers %d-%d"
	   ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
	   ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-line_pos)
	   ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-line_pos))) }

m1: /*ユーザー定義型*/
| DATA CAPID WHERE nl cons_decs { $5 }

m2:
| ID EQUAL QUESTION {$1}

cons_decs:
| cons_dec  cons_decs {$1 :: $2}
| cons_dec {[$1]}

cons_dec:
| CAPID COLON COLON texp nl  {($1,$4)}

fun_dec:
| ID COLON COLON texp nl {($1,$4)}

texp:
|tatom nl ALLOW nl texp {TFun ($1,$5)}
|CAPID tatoms { Data($1, $2) }
|tatom {$1}

tatom:
| INT {Int}
| BOOL {Bool}
| CAPID { Data($1, []) }
| LPAREN texp RPAREN { $2 }


tatoms:
| tatom tatoms { $1 :: $2 }
| tatom { [ $1 ] }

nl:
| NEWLINE nl {()}
| { () }

