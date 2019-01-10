type t = TScalar of basetype * Formula.t | TFun of (Id.t * t) * t | TBot
and basetype =
    TBool
  | TInt
  | TData of Id.t * t list * Formula.pa list
  | TVar of Formula.subst * Id.t
  | TAny of Id.t
          
type schema = Id.t list * (Id.t * Formula.pa_shape) list * t

type env
   
type contextual = TLet of env * t

type subst = t M.t                        

            

val free_tvar_base : basetype -> Id.t list
val free_tvar : t -> Id.t list
val genTvar : string -> t
val id2Tvar : Id.t -> t
val id2TAny : Id.t -> t
  
val extract_unknown_p : t -> S.t
val extract_unknown_p_base : basetype -> S.t
val t2string : t -> string
val b2string : basetype -> string
val t2string_sort : t -> string
val b2string_sort : basetype -> string
val b2sort : basetype -> Formula.sort option
val type2sort : t -> Formula.sort option
val schema2sort : schema -> Formula.sort option
val sort2type : Formula.sort -> t
val sort2type_base : Formula.sort -> basetype
val mk_mono_schmea : t -> schema
val schema2string : schema -> string

           
(* -------------------------------------------------- *)
(* environment *)
(* -------------------------------------------------- *)        
  
  
(* manupulation *)
val env2string :  env -> string
val env_empty : env
val env_add : env -> Id.t * t -> env
val env_add_list : env -> (Id.t * t) list -> env
val env_add_schema : env -> Id.t * schema -> env
val env_add_schema_list : env -> (Id.t * schema) list -> env
val env_add_F : env -> Formula.t -> env
val env_append : env -> env -> env
(* investigation *)
val env_find : env-> Id.t -> schema
val env_mem : env -> Id.t -> bool
val env_bindings : env-> Id.t list (* 名前変えたいな *)
val env_extract_bindings : env -> (Id.t * schema) list
val env_extract_unknown_p : env -> S.t
val env2formula : env -> S.t -> Formula.t
val env2formula_all : env -> Formula.t
val mk_sort_env : env -> Formula.Senv.t
  
(* -------------------------------------------------- *)
(* substitution *)
(* -------------------------------------------------- *)        

val substitute_F : Formula.subst -> t -> t
val substitute_T : subst -> t -> t
val substitute_pa : Formula.pa M.t -> t -> t
val env_substitute_F : Formula.subst -> env -> env
val replace_F : Id.t -> Id.t -> t -> t
val sort_subst2type : Formula.sort M.t -> t -> t
val alpha_fresh : t -> t
val instantiate_implicit : schema -> t list -> Formula.pa list -> t
val instantiate : env -> schema -> t
val mk_valid : Id.t -> basetype -> Formula.t


val mk_subst_for_const_var : env -> Formula.t M.t
val t_alpha_convert : t -> Id.t list -> t
val refresh_refinment : t -> t
