type t =
  |MLBool|MLInt
  |MLData of Id.t * (t list) 
  |MLVar of Id.t
  |MLFun of t * t

val shape: Type.t -> t

val string_of_t: t -> string

exception T2SORT
val t2sort: t -> Formula.sort
  
(* -------------------------------------------------- *)
(* schema *)
(* -------------------------------------------------- *)
  
type schema =  (Id.t list) *  t

val ty_of_schema: t -> schema

val ty_in_schema: schema -> t


val shape_sch: Type.schema -> schema

val string_of_sch: schema -> string


(*--------------------------------------------------*)
(* environment *)
(*--------------------------------------------------*)
type 'a env = (Id.t * 'a) list
            
val shape_env: Type.env -> schema env
  
val add_env: Id.t -> 'a -> 'a env -> 'a env

type 'a subst = 'a M.t              (* 肩変数のsubstitution *)



val subst_ty: t subst -> t -> t

val subst_sch: t subst -> schema -> schema

val subst_env: t subst -> schema env -> schema env

val subst_tasyn: t subst -> schema TaSyntax.t -> schema TaSyntax.t

val subst_compose: t subst -> t subst -> t subst
  



  
val infer: schema env -> Syntax.t -> (schema TaSyntax.t * t)

val ta_infer: schema env -> schema TaSyntax.t -> t
val ta_infer_e: schema env -> schema TaSyntax.e -> t
val ta_infer_b: schema env -> schema TaSyntax.b -> t
val ta_infer_f: schema env -> schema TaSyntax.f -> t
val ta_infer_case: schema env -> schema TaSyntax.case -> t    
  



  
