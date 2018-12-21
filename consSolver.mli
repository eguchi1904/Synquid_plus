module Liq = Type
module TaSyn = TaSyntax

exception SolvingErr of string

type p_assign = Formula.t list M.t
 
val find_predicate:
UseZ3.z3_env -> Qualifier.t list ->
Constraint.simple_cons list -> Liq.env -> Liq.t -> p_assign
 
(* val find_predicate2: *)
(*   p_assign -> Id.t list (\* priority *\) ->       *)
(*   Constraint.simple_cons list -> Liq.env -> Liq.t -> p_assign   *)
