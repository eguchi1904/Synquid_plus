
(* arg1: qualifiers
   arg2: type environment
   arg3:  program
   return: type of the program 
 *)
open Constraint
module Liq = Type
module TaSyn = TaSyntax
             

val liqInfer:  UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env
               -> Liq.schema TaSyntax.t -> Type.t

val f:  UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env ->
        Liq.t option TaSyn.t-> Liq.t
val f_check:  UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env ->
              Liq.t option TaSyn.t -> Liq.schema -> ((Id.t * Liq.t) list, string) result

val fEterm: UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env -> Syntax.e-> Liq.contextual


  

  
