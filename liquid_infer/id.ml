type t = string
let valueVar_id = "_v"
let counter = ref 0
let genid s =
  incr counter;
  Printf.sprintf "%s%d" s !counter

let pa_arg_prefix = "__"
let pa_arg_prefix_len = String.length pa_arg_prefix
                      
let counter2 = ref 0   
let gen_pa_arg ()=
  incr counter2;
  Printf.sprintf "%s%d" pa_arg_prefix !counter2

let is_pa_arg s =
  if String.length s >= pa_arg_prefix_len then
    pa_arg_prefix = (String.sub s 0 pa_arg_prefix_len)
  else
    false
