(* 
data list a <r::a -> a-> List> where
Nil::~~
Cons::~~
など、ユーザ定義データ型の情報を扱う
 *)

type t = {
    data_name: Id.t;
    type_param: Id.t list;
    pred_param: (Id.t * Formula.pa_shape) list;
    cons_list: ((Id.t * Type.schema) list)
         }

let mk_data_info :((Id.t * Type.schema) list -> t  M.t)
  = (fun env ->
    let rec which_data_cons  = function
      |Type.TScalar (Type.TData (i,_,_), _) -> i
      |Type.TFun (_,t) -> which_data_cons t
      |_ -> assert false
    in
    let rec mk_data_cons_list' env ans =
      match env with
      |(cons,(ts,ps,t) ):: left ->
        let data_type_id  = which_data_cons t in
        mk_data_cons_list' left (List_map.add data_type_id (cons, (ts,ps,t)) ans)
      |[] -> ans
    in
    let data_cons_list: ((Id.t * Type.schema) list) M.t =
      mk_data_cons_list' env M.empty in
    M.mapi
      (fun key cons_list ->
        match cons_list with
             |(cons, (ts,ps,_))::left ->
               {data_name = key;
                type_param = ts;
                pred_param = ps;
                cons_list = cons_list}
             |[] -> assert false
      )
    data_cons_list


  )


let param_2_string (ts: Id.t list) (ps:(Id.t * Formula.pa_shape) list) =
  let ts_string = String.concat " " ts in
  let ps_string = String.concat " "
                                (List.map
                                   (fun (p,pa_shape) ->
                                     Printf.sprintf "<%s::%s>"
                                                    p
                                                    (Formula.pashape2string pa_shape)
                                   )
                                   ps)
  in
  Printf.sprintf "%s %s" ts_string ps_string
                                
                                 
                                   
  
  
let rec data_info_2_string (data_info:t) =
  let head = Printf.sprintf "data %s %s where "
                           data_info.data_name
                           (param_2_string data_info.type_param data_info.pred_param)
  in
  let body =
    String.concat ""
      (List.map
         (fun (cons_name, (_,_,t)) ->
           let t = Type.refresh_refinment t in (* measure等の余計なrefinmentを除く *)
           Printf.sprintf " %s :: %s\n" cons_name (Type.t2string t))
         data_info.cons_list)
  in
  Printf.sprintf "%s\n%s" head body

let rec data_info_map_2_string (data_info_map:t M.t) =
  let data_str_list = 
    M.fold
      (fun key data_info acc ->
        (data_info_2_string data_info)::acc)
      data_info_map
      []
  in
  String.concat "\n\n" data_str_list
       
