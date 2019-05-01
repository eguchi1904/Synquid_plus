type t = string

val valueVar_id: t
val ignore_id: t

val genid: string -> t

(* predicate lambda expression's argument _0 _1 *)
val init_pa_arg_counter: unit -> unit

val gen_pa_arg: unit -> t

val is_pa_arg: t -> bool
