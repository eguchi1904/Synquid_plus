
(* arg1: qualifiers
   arg2: type environment
   arg3:  program
   return: type of the program 
 *)
module Liq = Type



val f: Formula.t list -> Liq.env -> Syntax.t -> Type.t
  
val liqInfer: Formula.t list -> Liq.env -> Ml.t TaSyntax.t -> Type.t


  

  
  
