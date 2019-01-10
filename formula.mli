type sort =
    BoolS
  | IntS
  | DataS of Id.t * sort list
  | SetS of sort
  | AnyS of Id.t
  | UnknownS of Id.t
type sort_subst = sort M.t
module Senv:
sig
  type t = private (Id.t * sort) list

  val empty : t
                   
  val cover : (Id.t * sort) list -> t
    
  val reveal : t -> (Id.t * sort) list    
    
  val add : t -> Id.t -> sort -> t

  val add_list : t -> (Id.t * sort) list -> t    

  val append : t -> t ->t

  val mem : Id.t -> t -> bool

  val mem2 : (Id.t * sort) -> t -> bool

  val of_string : t -> string    
end                

          
type t =
    Bool of bool
  | Int of int
  | Set of sort * t list
  | Var of sort * Id.t
  | Unknown of Senv.t * sort_subst * subst * Id.t
  | Cons of sort * Id.t * t list
  | UF of sort * Id.t * t list
  | All of (Id.t * sort) list * t
  | Exist of (Id.t * sort) list * t
  | If of t * t * t
  | Times of t * t
  | Plus of t * t
  | Minus of t * t
  | Eq of t * t
  | Neq of t * t
  | Lt of t * t
  | Le of t * t
  | Gt of t * t
  | Ge of t * t
  | And of t * t
  | Or of t * t
  | Implies of t * t
  | Iff of t * t
  | Union of t * t
  | Intersect of t * t
  | Diff of t * t
  | Member of t * t
  | Subset of t * t
  | Neg of t
  | Not of t

         
and subst = t M.t
type qformula =
    QAll of (Id.t * sort) list * t list * t
  | QExist of (Id.t * sort) list * t list
type pa = (Id.t * sort) list * t
val eta_shape : pa -> Id.t option
type pa_shape = sort list * sort
val p2string : t -> string
val sort2string : sort -> Id.t
val pashape2string : pa_shape -> Id.t
val p2string_with_sort : t -> string
val fv : t -> S.t
val fv_include_v : t -> S.t

val fv_sort : t -> (Id.t * sort) list

val fv_sort_include_v : t -> (Id.t * sort) list
val is_unknown_p : t -> bool
val extract_unknown_p : t -> S.t
val positive_negative_unknown_p : t -> (S.t * S.t * S.t)
  
val and_list : t list -> t
val list_and : t -> t list
val genFvar : sort -> string -> t
val id2pa_shape : Id.t -> pa_shape -> pa

val genUnknownP_explicit_id : Senv.t -> Id.t -> t
val genUnkownP : Senv.t -> Id.t -> t
val genUnknownPa : Senv.t -> pa -> Id.t -> pa
val genUnknownPa_shape : Senv.t -> pa_shape -> Id.t -> pa
  
val var_in_sort : sort -> S.t
val sort_subst : sort M.t -> sort -> sort
val compose_sort_subst : sort M.t -> sort M.t -> sort M.t
val sort_subst_to_shape : sort M.t -> pa_shape -> pa_shape
val sort_subst2formula : sort_subst -> t -> t
val sort_anyids : sort -> S.t
val any2unknownsort : sort -> sort
val any2unknownsort_pa : sort list * sort -> sort list * sort
exception Unify_Err
val unify_sort : (sort * sort) list -> sort M.t -> sort M.t
val subst_compose : subst -> subst -> t M.t
val substitution : subst -> t -> t
val pa_substitution : pa M.t -> t -> t
val replace : Id.t -> Id.t -> t -> t
val pa_replace : Id.t -> Id.t -> pa -> (Id.t * sort) list * t
val substitution_to_pa : t M.M.t -> pa -> pa
val pa2string : pa -> string
val pa2string_detail : pa -> string
