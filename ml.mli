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

val param_in_schema: schema -> Id.t list

val shape_sch: Type.schema -> schema

val string_of_sch: schema -> string


(*--------------------------------------------------*)
(* environment *)
(*--------------------------------------------------*)
type 'a env = (Id.t * 'a) list
            
val shape_env: Type.env -> schema env
  
val add_env: Id.t -> 'a -> 'a env -> 'a env


              
(*--------------------------------------------------*)
(* subtitution *)
(*--------------------------------------------------*)
  
type 'a subst = 'a M.t              (* 肩変数のsubstitution *)
              
val subst_ty: t subst -> t -> t

val subst_sch: t subst -> schema -> schema

val subst_refine_ty: Data_info.t M.t -> t M.t -> Type.t -> Type.t

val subst_env: t subst -> schema env -> schema env

val subst_tasyn: t subst -> schema TaSyntax.t -> schema TaSyntax.t

val subst_compose: t subst -> t subst -> t subst

(*--------------------------------------------------*)
(* utils *)
(*--------------------------------------------------*)

val mk_refine_top: Data_info.t M.t -> t -> Type.t
  
val mk_refine_top_sch: Data_info.t M.t -> schema -> Type.schema

val mk_refine_bot: Data_info.t M.t -> t -> Type.t
  
val mk_refine_bot_sch: Data_info.t M.t -> schema -> Type.schema  


val mk_refine_ignore: Data_info.t M.t -> t -> Type.t
  
val mk_refine_ignore_sch: Data_info.t M.t -> schema -> Type.schema  
  
(*--------------------------------------------------*)
(* type inference *)
(*--------------------------------------------------*)
exception ML_Inf_Err of string
val unify2: t -> t -> t subst
val infer: schema env -> (t option) TaSyntax.t -> (schema TaSyntax.t * t)
val check: schema env -> (t option) TaSyntax.t -> t -> schema TaSyntax.t 

val ta_infer: schema env -> schema TaSyntax.t -> t
val ta_infer_e: schema env -> schema TaSyntax.e -> t
val ta_infer_b: schema env -> schema TaSyntax.b -> t
val ta_infer_f: schema env -> schema TaSyntax.f -> t
val ta_infer_case: schema env -> schema TaSyntax.case -> t    
  



  
