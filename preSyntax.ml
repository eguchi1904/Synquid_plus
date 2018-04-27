type extend_pa_shape = (Formula.sort list) * Formula.sort * (Formula.t option)
(* List a -> {Int | _v >= 0} などの、measureにつく謎表記に対応する型 *)
let extend2shape ((args, rets, _):extend_pa_shape):Formula.pa_shape = (args, rets)
type measureCase = {constructor : Id.t ; args : Id.t list ; body : Formula.t }
(* type measureInfo = (Id.t *(Formula.pa_shape *  measureCase list) ) (\* 一つのmeasureのinfo *\) *)
type measureInfo = {name: Id.t;
                    shape: extend_pa_shape;
                    cases: measureCase list;
                    termination:bool}
                 
type id_schemas =  (Id.t * Type.schema) list 

let rec mk_args free_v i =
  let v = Printf.sprintf "_%d" i in
  if List.mem_assoc v free_v then
    let s = List.assoc v free_v in
    (v,s)::(mk_args free_v (i+1) )
  else
    []

(* parser.mlyで使用 *)
let rec pop_lst = function
 |[] -> assert false
 |[x] -> [],x
 |x::xs ->let xs',v =  pop_lst xs in
           (x::xs', v)
   
(* r _0 _1 --> \0.\1.r 0 1 *)
let formula2pa  p =
  let free_v = Formula.fv_sort p in
  let args = mk_args free_v 0 in
  (args,p)
  
(* parser.mlyで使用 *)
let mk_measureCase x y z =   
  {constructor= x; args = y; body = z }
  
(* parser.mlyで使用 *)
let mk_measureInfo name
                   (sorts, refinement:(Formula.sort list * (Formula.t option)))
                   (cases:measureCase list)
                   is_term=
  let arg_sort, rets = pop_lst sorts in
  let measure_shape:extend_pa_shape = (arg_sort, rets, refinement) in
  {name = name; shape = measure_shape; cases = cases; termination = is_term}
  
  

let rec extend_pashape2string (args, rets, refinement) =
  match args with
  |s::left -> Printf.sprintf "%s -> %s"
                             (Formula.sort2string s)
                             (extend_pashape2string (left,rets, refinement))
  |[] ->
    (match refinement with
     |Some formula ->
       Printf.sprintf "{%s | %s}" (Formula.sort2string rets) (Formula.p2string formula)
     |None -> Formula.sort2string rets)

let minfo2string ({name=measure; shape = shape; cases=cases; termination = is_term}:measureInfo) =
  let head =
    (if is_term then
      Printf.sprintf "termination measure %s::%s where" measure (extend_pashape2string shape)
     else
       Printf.sprintf "measure %s::%s where" measure (extend_pashape2string shape))
  in
  let case2str {constructor = cons; args = args; body = body } =
    Printf.sprintf " %s %s -> %s" cons (String.concat " " args) (Formula.p2string body)
  in
  let body = String.concat "\n" (List.map case2str cases) in
  Printf.sprintf "%s \n%s" head body

let minfo_list_2_string (minfos: measureInfo list) =
  String.concat "\n\n" (List.map minfo2string minfos)

  
