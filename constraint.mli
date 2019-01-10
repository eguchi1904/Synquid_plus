module Liq = Type
           
exception Constraint of string

(* -------------------------------------------------- *)
(* type constraint: well formedness / subtyping  *)
(* -------------------------------------------------- *)                          
type cons = WF of (Liq.env * Liq.t) | Sub of (Liq.env * Liq.t * Liq.t)


val subst_cons : Formula.subst -> cons -> cons
  
val cons2string : cons -> string
val cons2string_human : cons -> string
val cons_list_to_string : cons list -> string
val cons_list_to_string_human : cons list -> string



(* -------------------------------------------------- *)
(* formula constraints: well formedness / implication  *)
(* -------------------------------------------------- *)                            
type simple_cons = |SWF of Liq.env * ((Id.t * Formula.sort) list * Formula.t) 
                   |SSub of (Liq.env * Formula.t * Formula.t)
                          

val split_cons : cons -> simple_cons list

  
val is_valid_simple_cons : UseZ3.z3_env -> simple_cons -> bool
(* unknown p に対するsubst *)
val subst_simple_cons : Formula.subst -> simple_cons -> simple_cons
val unknown_p_in_simple_cons : simple_cons -> S.t
val is_predicate_normal_position : simple_cons -> bool
val positive_negative_unknown_p : simple_cons -> (S.t * S.t * S.t)

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

  










                                   
