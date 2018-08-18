
open Type
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

(* special case of t   -- list  with measure len and elems*)
type t_list = {
    data_name: Id.t;
    type_param: Id.t list;
    pred_param: (Id.t * Formula.pa_shape) list;
    cons:Id.t;
    nil:Id.t;
    len: PreSyntax.measureInfo;
    elems:PreSyntax.measureInfo
  }       

(* special case of t   -- pair with measure fst snd *)          
type t_pair = {
    data_name: Id.t;
    type_param: Id.t list;
    pred_param: (Id.t * Formula.pa_shape) list;
    pair:Id.t;
    fst: PreSyntax.measureInfo;
    snd: PreSyntax.measureInfo 
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

  
(* 
instantiate_pred_param_shape
Example

input1
----------------------------------------
List a <r:: a -> a -> Bool>
 |~~
 |~~

input2
----------------------------------------
a = {Int| _v > 0}

output
----------------------------------------
r:: Int -> Int -> Bool

 *)
let instantiate_pred_param_shape  {data_name = _;
                                   type_param = ty_param;
                                   pred_param = p_param;
                                   cons_list = _}
                                  (tys:Type.t list) =
  
    let sita_sort_list = List.map2 (fun a ty -> (a, Type.type2sort ty))
                                   ty_param
                                   tys
    in
    let sita_sort = List.fold_left
                      (fun acc a_sort ->
                        match a_sort with
                        |(a, None) -> acc
                        |(a, Some sort) -> M.add a sort acc)
                      M.empty
                      sita_sort_list
    in
    List.map
      (fun (r, shape) ->  (r, (Formula.sort_subst_to_shape sita_sort shape) ))
      p_param

let adjust_pa_shape ((args, t):Formula.pa) ((arg_sort, sort):Formula.pa_shape) =
  let new_args = List.combine (List.map fst args) arg_sort in
  let sita_sort_list = List.combine (List.map snd args) arg_sort in
  let sita_sort = List.fold_left
                    (fun acc (s1,s2) ->
                      match s1 with
                      |Formula.AnyS i -> M.add i s2 acc
                      |_ -> acc)
                    M.empty
                    sita_sort_list
  in
  let new_t = Formula.sort_subst2formula sita_sort t in
  (new_args, new_t)
                                          
let rec fix_sort_in_pred_param datainfo_map ty = match ty with
  |TScalar (TData (i, tys, pas), p) ->
    let datainfo = M.find i datainfo_map in
    let pa_shape_list = instantiate_pred_param_shape datainfo tys in
    let pas' =
      List.map2 adjust_pa_shape pas (List.map snd pa_shape_list)
    in
    let tys' = List.map (fix_sort_in_pred_param datainfo_map) tys in
    TScalar (TData (i, tys', pas'), p)
  |TScalar (b, p) -> TScalar (b, p)
  |TFun ((x, ty1), ty2) ->
    let ty1' = fix_sort_in_pred_param datainfo_map ty1 in
    let ty2' = fix_sort_in_pred_param datainfo_map ty2 in
    TFun ((x, ty1'), ty2')
  |TBot -> TBot

let fix_sort_in_pred_param_schema datainfo_map (alist,pas, ty) =
  (alist,pas, fix_sort_in_pred_param datainfo_map ty)
                                             
  

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
       

exception Data_List of string

let is_list_nil data_name (_, _, t) =
  match t with
  |TScalar ( (TData (id, _,_)), _) when id = data_name ->
    true
  |_ -> false

let is_list_cons data_name (_, _, t) =
  match t with
  (* 第１引数が再帰ならfalse *)
  |TFun ((_, TScalar( TData(id,_,_), _)),_)
       when id = data_name ->
    false
  |TFun ((_,t1),
         TFun ( (_,TScalar ((TData (id2,_,_)),_) ),
               TScalar( TData(id3,_,_), _)
        ))
       when id2 = data_name && id3 = data_name ->
    true
  |_ -> false
         
  
                
let is_list: t -> (t * Id.t * Id.t) option = (* listならdata_name,nil,consに当たるコンストラクたを返す *)
  (fun data ->
    let data_name = data.data_name in
    match data.cons_list with
    |[(nil, nil_t); (cons, cons_t) ] 
         when (is_list_nil data_name nil_t)&&
                (is_list_cons data_name cons_t) ->
      Some (data, nil, cons)
    | [(cons, cons_t); (nil, nil_t)]
             when (is_list_nil data_name nil_t)&&
                    (is_list_cons data_name cons_t) ->
       Some (data, nil, cons)
    |_ -> None
  )

  
let extract_list: t M.t -> PreSyntax.measureInfo list -> (t_list* t M.t * PreSyntax.measureInfo list)  =
  (fun data_info_map minfos ->
    let list_cons_nil_map = M.map is_list data_info_map in
    let list_cons_nil =
      M.fold
        (fun data_name option acc ->
          (match acc with
           |Some _ -> acc
           |None -> option))
        list_cons_nil_map
        None
    in
    match list_cons_nil with
    |None -> raise (Data_List "there are no data type list")
    |Some (data, nil, cons)->
      let len_info =List.find PreSyntax.is_len minfos in
      let elems_info = List.find PreSyntax.is_elems minfos in
      {data_name= data.data_name;
       type_param= data.type_param;
       pred_param= data.pred_param;
       cons= cons;
       nil = nil;
       len = len_info;
       elems = elems_info
      },
      data_info_map,
      minfos
      
  )      
      


(* 以下、pair *)

(* a -> b -> pair a b の形か *)
let is_pair_cons data_name (_, _, t) =
  match t with
  (* 第１引数が再帰ならfalse *)
  |TFun ((_,TScalar ( TVar(_,a), _)),
         TFun ( (_,TScalar ( TVar(_,b), _)),
               TScalar( TData(id,[TScalar ( TVar(_,c), _); TScalar ( TVar(_,d), _)],_), _)
        ))
       when id = data_name && a = c && b = d ->
    true
  |_ -> false
         
  
                
let is_pair: t -> (t * Id.t ) option = (* listならdata,pair_consに当たるコンストラクたを返す *)
  (fun data ->
    let data_name = data.data_name in
    match data.cons_list with
    |[(pair_cons, cons_t)]
      when (is_pair_cons data_name cons_t) ->
      Some (data, pair_cons)
    | _ -> None
  )

  
let extract_pair: t M.t -> PreSyntax.measureInfo list -> (t_pair* t M.t * PreSyntax.measureInfo list)  =
  (fun data_info_map minfos ->
    let pair_cons_map = M.map is_pair data_info_map in
    let pair_cons =
      M.fold
        (fun data_name option acc ->
          (match acc with
           |Some _ -> acc
           |None -> option))
        pair_cons_map
        None
    in
    match pair_cons with
    |None -> raise (Data_List "there are no data type list")
    |Some (data, pair_cons)->
      let fst_info =List.find PreSyntax.is_fst minfos in
      let snd_info = List.find PreSyntax.is_snd minfos in
      
      {data_name= data.data_name;
       type_param= data.type_param;
       pred_param= data.pred_param;
       pair = pair_cons;
       fst = fst_info;
       snd = snd_info
      },
      data_info_map,
      minfos
      
  )      
          
      
      
