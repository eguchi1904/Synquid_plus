type t = string
let valueVar_id = "_v"
let counter = ref 0
let genid s =
  incr counter;
  Printf.sprintf "%s%d" s !counter

let pa_arg_prefix = "_"
let pa_arg_prefix_len = String.length pa_arg_prefix
                      
let counter2 = ref 0
let init_pa_arg_counter () = counter2 := 0
                           
let gen_pa_arg ()=
  let id =   Printf.sprintf "%s%d" pa_arg_prefix !counter2 in
  (incr counter2);
  id

let is_pa_arg s =
  if String.length s >= pa_arg_prefix_len then
    pa_arg_prefix = (String.sub s 0 pa_arg_prefix_len)
  else
    false
