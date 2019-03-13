type t = string

(* private module for saving correspoindans of string id and integer id *)
module Table = struct
  let to_int_hash:(string, int) Hashtbl.t = Hashtbl.create 100
  let to_str_hash:(int, string) Hashtbl.t = Hashtbl.create 100
  let add str i =
    let () = Hashtbl.add to_str_hash i str in
    let () = Hashtbl.add to_int_hash str i in
    ()

  let find_int str = Hashtbl.find to_int_hash str
  let find_str i = Hashtbl.find to_str_hash i
    
end

       
let valueVar_id = "_v"
let counter = ref 0
let genid s =
  incr counter;
  let int_id = !counter in
  let str_id = Printf.sprintf "%s%d" s !counter in
  let () = Table.add str_id int_id in
  str_id

let to_int str =
  try
    Table.find_int str
  with
    Not_found -> invalid_arg "Id.to_int: this string is not generated id"

let of_int i =
  try
    Table.find_str i
  with
    Not_found -> invalid_arg "Id.to_int: this number is not generated id"               

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

