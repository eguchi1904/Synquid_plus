
(* arg1: qualifiers
   arg2: type environment
   arg3:  program
   return: type of the program 
 *)
open Constraint
module Liq = Type
module TaSyn = TaSyntax
             

val liqInfer:  UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env -> Ml.schema TaSyntax.t -> Type.t

val f:  UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env -> Syntax.t-> Liq.t
val f_check:  UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env -> Syntax.t-> Liq.schema -> bool

val fEterm: UseZ3.z3_env -> Data_info.t M.t -> Qualifier.t list -> Liq.env -> Syntax.e-> Liq.contextual
     
  

  
  
