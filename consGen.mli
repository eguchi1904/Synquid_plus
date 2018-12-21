module Liq = Type
module TaSyn = TaSyntax

exception ConsGenErr of string

val fresh : Data_info.t M.t -> Ml.t -> Constraint.Liq.t
  
val mk_tmp :
  Data_info.t M.t -> Type.env -> Ml.schema TaSyntax.t -> Liq.t

(* generate refinement type template from ML type *)
val fresh: Data_info.t M.t -> Ml.t -> Liq.t 

(* 
  "cons_gen data_info env t ty" generate constraint to satisfy
  env |- t :: ty
 *)
val cons_gen: Data_info.t M.t -> Liq.env -> Ml.schema TaSyn.t -> Liq.t -> (Liq.t * Constraint.cons list)

val cons_gen_infer: Data_info.t M.t -> Liq.env -> Ml.schema TaSyn.t  -> (Liq.t * Constraint.cons list)
  

val cons_gen_e :
  Data_info.t M.t ->
  Liq.env ->
  Ml.schema TaSyn.e -> Constraint.Liq.contextual * Constraint.cons list
val cons_gen_b :
  Data_info.t M.t ->
  Liq.env ->
  Ml.schema TaSyn.b ->
  Constraint.Liq.t -> Constraint.Liq.t * Constraint.cons list
val cons_gen_case :
  Data_info.t M.t ->
  Liq.env ->
  Liq.t ->
  Liq.contextual -> Ml.schema TaSyn.case -> Constraint.cons list
val cons_gen_f :
  Data_info.t M.t ->
  Liq.env ->
  Ml.schema TaSyn.f ->
  Liq.t -> Liq.t * Constraint.cons list

(* -------------------------------------------------- *)
(* logging  *)
(* -------------------------------------------------- *)


val log_simple_cons : string -> Constraint.simple_cons list -> unit

  
  
  
