type t = {
  data_name : Id.t;
  type_param : Id.t list;
  pred_param : (Id.t * Formula.pa_shape) list;
  cons_list : (Id.t * Type.schema) list;
}
type t_list = {
  data_name : Id.t;
  type_param : Id.t list;
  pred_param : (Id.t * Formula.pa_shape) list;
  cons : Id.t;
  nil : Id.t;
  len : PreSyntax.measureInfo;
  elems : PreSyntax.measureInfo;
}
type t_pair = {
  data_name : Id.t;
  type_param : Id.t list;
  pred_param : (Id.t * Formula.pa_shape) list;
  pair : Id.t;
  fst : PreSyntax.measureInfo;
  snd : PreSyntax.measureInfo;
}
val mk_data_info : (Id.t * Type.schema) list -> t M.t

val instantiate_pred_param_shape : t -> Type.t list -> (Id.t * Formula.pa_shape) list

val fix_sort_in_pred_param_schema: t M.t -> Type.schema -> Type.schema
  
val param_2_string : Id.t list -> (Id.t * Formula.pa_shape) list -> string
val data_info_2_string : t -> string
val data_info_map_2_string : t M.t -> string
exception Data_List of string
val is_list_nil : Id.t -> 'a * 'b * Type.t -> bool
val is_list_cons : Id.t -> 'a * 'b * Type.t -> bool
val is_list : t -> (t * Id.t * Id.t) option
val extract_list :
  t M.t ->
  PreSyntax.measureInfo list -> t_list * t M.t * PreSyntax.measureInfo list
val is_pair_cons : Id.t -> 'a * 'b * Type.t -> bool
val is_pair : t -> (t * Id.t) option
val extract_pair :
  t M.t ->
  PreSyntax.measureInfo list -> t_pair * t M.t * PreSyntax.measureInfo list
