
(* arg1: qualifiers
   arg2: type environment
   arg3:  program
   return: type of the program 
 *)

module Liq = Type
module TaSyn = TaSyntax
             
type qualifier = Formula.t
               
type cons = |WF of (Liq.env * Liq.t)           (* well formendness *)
            |Sub of (Liq.env * Liq.t * Liq.t ) (* subtyping *)

                  
  

val fresh: Data_info.t M.t -> Ml.t -> Liq.t 
                  
val cons_gen: Data_info.t M.t -> Liq.env -> Ml.schema TaSyn.t -> (Liq.t * cons list)


  
val liqInfer:  UseZ3.z3_env -> Data_info.t M.t -> Formula.t list -> Liq.env -> Ml.schema TaSyntax.t -> Type.t

val f:  UseZ3.z3_env -> Data_info.t M.t -> Formula.t list -> Liq.env -> Syntax.t-> Liq.t
  

  
  
