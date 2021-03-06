module Liq = Type
           
exception Constraint of string

(* -------------------------------------------------- *)
(* type constraint: well formedness / subtyping  *)
(* -------------------------------------------------- *)                          
type cons = |WF of (Liq.env * Liq.t)
            |Sub of {body: (Liq.env * Liq.t * Liq.t)
                    ;defining: Liq.env}                                           


val subst_cons : Formula.subst -> cons -> cons
  
val cons2string : cons -> string
val cons2string_human : cons -> string
val cons_list_to_string : cons list -> string
val cons_list_to_string_human : cons list -> string



(* -------------------------------------------------- *)
(* formula constraints: well formedness / implication  *)
(* -------------------------------------------------- *)
type simple_cons =
  (* SWF:: env,senv|-phi, envは、制約生成時の型環境。 *)
  |SWF of Liq.env * (Formula.Senv.t * Formula.t) 
  |SSub of {body:(Liq.env * Formula.t * Formula.t)
           ;defining:Liq.env}  
                          

val split_cons : cons -> simple_cons list

(* using LIq.env2formula *)
val is_valid_simple_cons : simple_cons -> bool
(* using Liq.env2formula_all *)
val is_valid_simple_cons_all : simple_cons -> bool
(* using Liq.env2formula_all *)
val is_satisifiable_simple_cons_all : simple_cons -> bool

val replace_ignore : simple_cons -> simple_cons
val remove_ignore : simple_cons list -> simple_cons list
val remove_dummy_loop : simple_cons list -> simple_cons list  
val remove_obviously_valid : simple_cons list -> simple_cons list

val add_dummy_start_point_constraint : simple_cons list -> simple_cons list
  
(* unknown p に対するsubst *)
val subst_simple_cons : Formula.subst -> simple_cons -> simple_cons
val unknown_p_in_simple_cons : simple_cons -> S.t
val replace_unknown_p_to_top : simple_cons -> simple_cons
val defining_unknown_in_simple_cons : simple_cons -> S.t
  
val is_predicate_normal_position : simple_cons -> bool
val positive_negative_unknown_p : simple_cons -> (S.t * S.t * S.t)
val mk_qformula_from_positive_cons : Liq.env -> Id.t -> simple_cons -> Formula.qformula
val mk_qformula_from_negative_cons : Liq.env -> Id.t -> simple_cons -> Formula.qformula

val scons2string : simple_cons -> string
val scons2string_human : Formula.subst -> simple_cons -> string  
val scons_list_to_string : simple_cons list -> string

(* -------------------------------------------------- *)
(* (pure)formula constraints : well formedness / implication  *)
(* -------------------------------------------------- *)                              
type pure_simple_cons =
  PSWF of ((Id.t * Formula.sort) list * Formula.t)
  |PSSub of (Formula.t * Formula.t * Formula.t)

val inst_scons :
  Formula.subst -> simple_cons -> Formula.t * Formula.t * Formula.t

  










                                   
