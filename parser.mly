%{

open Type
open Formula
open Syntax
open PreSyntax




let sdummy = IntS

let rec pop_lst = function
 |[] -> assert false
 |[x] -> [],x
 |x::xs ->let xs',v =  pop_lst xs in
           (x::xs', v)
 
%}

%token LET
%token DATA
%token WHERE
%token MEASURE
%token TERMINATION
%token INTSYMBOL
%token BOOLSYMBOL
%token EQUAL
%token NEQUAL
%token NOT
%token AND
%token OR
%token IMPLIES
%token IFF
%token LESS
%token LESS_EQUAL
%token GREATER
%token GREATER_EQUAL
%token MINUS
%token PLUS
%token AST
%token IN
%token IF
%token THEN
%token ELSE
%token MATCH
%token WITH
%token SET
%token ALLOW
%token COLON
%token QUESTION
%token LPAREN
%token RPAREN
%token LSQBRAC
%token RSQBRAC
%token LCURBRAC
%token RCURBRAC
%token PIPE
%token BACKSLASH
%token DOT
%token COMMA
%token VALVAR
%token TRUE
%token FALSE
%token <int> INT
%token <Id.t> AUXI
%token <Id.t> ID
%token <Id.t> IDCOLONCOLON
%token <Id.t> CAPID
%token EOF
%token NEWLINE

%left prec_app
%left AND OR IFF IMPLIES 
%left EQUAL NEQUAL
%left MINUS PLUS IN
%left AST

%type < PreSyntax.id_schemas * PreSyntax.measureInfo list * PreSyntax.id_schemas * ((Id.t * Syntax.t) list) > toplevel
%type <PreSyntax.id_schemas> m1 /*m1によってコンストラクタの型の環境を作成*/
%type <Id.t list> t_paras
%type <(Id.t * Formula.pa_shape) list> p_paras

%type <Id.t * Type.t> cons_dec
%type <Id.t * Type.schema> fun_dec

%type < PreSyntax.measureInfo > m2

%type < Formula.sort list > sort_shape
%type < Formula.sort list * Formula.t option > extend_sort_shape
%type < PreSyntax.measureCase > case
%type <Type.t> texp
%type <Formula.t> fexp
%start toplevel

%%

toplevel:
| NEWLINE toplevel
  { $2 }
| m1 toplevel
{ match ($2) with
    (env, minfos, fundecs, l) -> ($1@env, minfos, fundecs, l)
}
| fun_dec toplevel
 { match ($2) with
   (env, minfos, fundecs, l) -> (env, minfos, $1::fundecs, l)
   }
| m2 toplevel
 { match ($2) with
   (env, minfos, fundecs, l) -> (env, $1::minfos, fundecs, l)
   }
| m3 toplevel
 { match ($2) with
   (env, minfos, fundecs, l) -> (env, minfos, fundecs, $1::l)
   }

| EOF
    { ([],[],[],[])}

| error
    { failwith
     (let line_pos=(Parsing.symbol_start_pos ()).Lexing.pos_bol in
	(Printf.sprintf "parse error near line %d charactfers %d-%d"
	   ((Parsing.symbol_start_pos ()).Lexing.pos_lnum)
	   ((Parsing.symbol_start_pos ()).Lexing.pos_cnum-line_pos)
	   ((Parsing.symbol_end_pos ()).Lexing.pos_cnum-line_pos))) }





m1: /*ユーザー定義型*/
| DATA CAPID t_paras p_paras WHERE nl  cons_decs
{ List.map (fun (id,t) -> (id,($3,$4,t) ) ) $7

  }


t_paras:
| ID t_paras { $1 :: $2 }
| { [] }

p_paras:
| LESS ID COLON COLON sort_shape GREATER p_paras /* e.g. < r :: a -> a -> Int> */
 { 
 ($2, pop_lst $5) :: $7 }
|  { [] }

cons_decs:
| cons_dec cons_decs {$1 :: $2}
| cons_dec {[$1]}

cons_dec:
| CAPID COLON COLON texp nl {($1,$4)}


/*function type declaration */

fun_dec:
| ID COLON COLON p_paras DOT texp nl /*f :: <r :: a ->Bool>. ~~*/
  { ($1,( (Type.free_tvar $6), $4, $6) )}
| ID COLON COLON texp nl /*f:: ~~ */
  { ($1, ( (Type.free_tvar $4), [], $4)) }


/*measure definition*/
m2:
| MEASURE ID COLON COLON extend_sort_shape WHERE nl cases
 { mk_measureInfo $2 $5 $8 false }
| TERMINATION MEASURE ID COLON COLON extend_sort_shape WHERE nl cases
 { mk_measureInfo $3 $6 $9 true } 

cases:
|case cases { $1 :: $2 }
| { [] }

case: 
| CAPID cargs ALLOW fexp nl
 { mk_measureCase $1 $2 $4 }

cargs:
| ID cargs { $1 :: $2 }
| { [] }


m3:/* query */
| ID nl EQUAL nl prg nl
{
 match $5 with
  |PF f -> ($1, PF (PFix ($1, f)))
  | _ -> ($1, $5)
}


prg:
| LPAREN prg RPAREN { $2 }
| prg_e { PE $1 }
| prg_b { PI $1 }
| prg_f { PF $1 }
| LET nl ID nl EQUAL nl prg nl IN nl prg { PLet ($3, $7, $11) }
| QUESTION { PHole }

prg_e:
|prg_eatom { $1 }
| prg_e prg_eatom  %prec prec_app
  { PAppFo( $1, $2 ) }
| prg_e prg_f  %prec prec_app
  { PAppHo( $1, $2 ) }  
  
prg_eatom:
| LPAREN prg_e RPAREN { $2 }
| ID { PSymbol $1 }
| CAPID { PSymbol $1 }
| AUXI { PAuxi $1 }

prg_b:
| LPAREN prg_b RPAREN { $2 }
| IF nl prg_e nl THEN nl prg nl ELSE nl prg { PIf ($3, $7, $11) }
| MATCH prg_e WITH nl prg_cases  { PMatch ($2, $5) }

prg_cases:
| prg_case prg_cases { $1 :: $2 }
| prg_case { [$1] }

prg_case:
| CAPID cargs ALLOW prg nl { Syntax.mk_case $1 $2 $4 }

prg_f:
|  LPAREN prg_f RPAREN { $2 }
| BACKSLASH ID DOT nl  prg { PFun ($2, $5) }





/* sort shape */

sort_shape:
| sortatom ALLOW sort_shape  { $1 :: $3 }
| sortatom { [$1] }
| LCURBRAC sortatom PIPE fexp RCURBRAC /* {Int | _v > 0} */
  { [$2] }

sortatoms:
| sortatom sortatoms { $1 :: $2 }
| { [] }

sortatom:
| BOOLSYMBOL { BoolS }
| INTSYMBOL { IntS }
| ID { AnyS $1 }
| SET sortatom { SetS $2 }
| CAPID sortatoms { DataS ($1, $2) }

extend_sort_shape:
|sortatom ALLOW extend_sort_shape
 { match $3 with (args, refinment) -> ($1::args, refinment) }
|sortatom { ([$1], None) }
| LCURBRAC sortatom PIPE fexp RCURBRAC /* {Int | _v > 0} */
  { [$2], Some $4 }

/*type syntax*/

texp:
|ID COLON tatom nl ALLOW nl texp {TFun (($1,$3), $7) } /* x:t1 -> t2 */
|tatom {$1}

tatom:
| LPAREN texp RPAREN { $2 }
| LCURBRAC basetype PIPE fexp RCURBRAC /*{b | p}の形*/
 { TScalar ($2, $4) }
| basetype { TScalar ($1, Bool true) }  /*refinmentが略記されたもの*/


basetype:
| INTSYMBOL {TInt}
| BOOLSYMBOL {TBool}
| CAPID tatoms pas { TData($1, $2, $3) }
| ID { TAny $1 }

tatoms:
| tatom tatoms  { $1 :: $2 }
|  { [] }

/*predicate abstraction */
pas:
| pa pas {$1 :: $2}
|  { [] }

pa:
| LESS LCURBRAC fexp RCURBRAC GREATER /* <{r _0 _1}> */
 { ([], $3) }
| LESS ID GREATER /* <r> 略記*/
 { ([($2, sdummy)], Unknown(M.empty, M.empty, $2) ) }  /*dummy*/



/* logical formula syntax */

fatom:
| TRUE {Bool true }
| FALSE {Bool false }
| INT {Int $1 }
| setliteral {$1}
| VALVAR { Var (sdummy, Id.valueVar_id) }
| ID { Var (sdummy, $1) }
| LPAREN fexp RPAREN { $2 }


fexp:
| fatom {$1}
| ID funargs { UF (sdummy, $1, $2) } 
| CAPID funargs { Cons (sdummy, $1, $2) } 
| IF fexp THEN fexp ELSE fexp { If ($2, $4, $6) }
| fexp AST fexp { Times ($1, $3) }  /* int_mul or set_intersection, decide later*/
| fexp PLUS fexp { Plus ($1, $3) }   /*int_plus or set_union, decide later*/
| fexp MINUS fexp { Minus ($1, $3) }  /*int_minus of set_diff, decide later*/
| fexp EQUAL EQUAL fexp { Eq ($1, $4) }
| fexp NEQUAL fexp { Neq ($1, $3) }
| fexp LESS fexp { Lt ($1, $3) }
| fexp LESS_EQUAL fexp { Le ($1, $3) } /*Le of set_subset, decide later*/
| fexp GREATER fexp { Gt ($1, $3) }
| fexp GREATER_EQUAL fexp { Ge ($1, $3) }
| fexp AND fexp { And ($1, $3) }
| fexp OR fexp { Or ($1, $3) }
| fexp IMPLIES fexp { Implies ($1, $3) }
| fexp IFF fexp { Iff ($1, $3) }
| fexp IN fexp { Member ($1, $3) }
| MINUS fexp { Neg $2 }
| NOT fexp { Not $2 }

setliteral:
| LSQBRAC fcommas RSQBRAC { Set (sdummy, $2) }
fcommas:
| { [] }
| fexp  { [$1] }
| fexp COMMA fcommas { $1 :: $3 }

funargs:
| fatom funargs { $1 :: $2 }
| fatom { [$1] }

nl:
| NEWLINE nl { () }
| { () }
