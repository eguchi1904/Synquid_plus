type t = string

val valueVar_id: t

val genid: string -> t

(* of_int to_int = identity func *)
val to_int: t -> int
val of_int: int -> t
  

(* predicate lambda expression's argument _0 _1 *)
val init_pa_arg_counter: unit -> unit

val gen_pa_arg: unit -> t

val is_pa_arg: t -> bool
