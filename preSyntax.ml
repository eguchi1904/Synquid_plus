type measureCase = {constructor : Id.t ; args : Id.t list ; body : Formula.t }
type measureInfo = (Id.t *(Formula.pa_shape *  measureCase list) ) (* 一つのmeasureのinfo *)
type id_schemas =  (Id.t * Type.schema) list 

let rec mk_args free_v i =
  let v = Printf.sprintf "_%d" i in
  if List.mem_assoc v free_v then
    let s = List.assoc v free_v in
    (v,s)::(mk_args free_v (i+1) )
  else
    []
                 
(* r _0 _1 --> \0.\1.r 0 1 *)
let formula2pa  p =
  let free_v = Formula.fv_sort p in
  let args = mk_args free_v 0 in
  (args,p)

let mk_measureCase x y z =   
{constructor= x; args = y; body = z }

let minfo2string ((measure, (shape, _)):measureInfo) =
  Printf.sprintf "%s::%s" measure (Formula.pashape2string shape)
  
