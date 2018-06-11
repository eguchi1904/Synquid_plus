open Extensions
open Syntax
open Type
type data_type_arg_info = {name:Id.t; nth:int; data_id:Id.t}

let gen_g_id () = Id.genid "g_"
                        
let rec pop_data_type_arg': Type.t ->
                            (data_type_arg_info) option * Id.t list * bool * int ->
                            (data_type_arg_info * (Id.t list)) option
  =
  (fun t (fst_data_arg_info, other_args, found, i) ->
  match t with
  |TFun ((x, (TScalar (TData (id, _, _), _))), t2) when (not found)->
    pop_data_type_arg' t2 (Some {name=x; nth=i; data_id=id}, other_args, true, (i+1))
  |TFun ((x,t1),t2) ->
    pop_data_type_arg' t2 (fst_data_arg_info, (x::other_args), found, (i+1))
  |TScalar _ ->
    (match fst_data_arg_info with
     |Some info -> Some (info, other_args)
     |None -> None
    )
  |TBot -> assert false)

(* pop_data_type_arg t -> (fst_data_type_info, othere_args) 

fst_data_type_info: データ型引数の情報、data_type_arg_info型
other_args: それ以外の引数リスト
 *)
let pop_data_type_arg : Type.t -> (data_type_arg_info * (Id.t list)) option =
  fun t ->
  pop_data_type_arg' t (None, [], false, 0)


let rec type_args t =           (* first-order fun type *)
  match t with
  |TScalar _ -> []
  |TFun ((x,t1),t2) -> (x,t1)::(type_args t2)
  |TBot -> assert false

(* 型に合った、fold型のテンプレートを生成 *)
let fold: Data_info.t M.t -> PreSyntax.measureInfo list -> Id.t -> Type.schema -> Syntax.t =
  (fun  data_info_map _ f_name (_,_,goal_t) ->
      match pop_data_type_arg goal_t with
       |Some ({name=x; nth=x_nth; data_id= data}, othere_args) ->
         let app_f y =          (* fを再帰適用する項を作る *)
           let args = List.insert y x_nth othere_args in
           mk_fun_app_term (PSymbol f_name) args
         in
         let is_recursive_type t = (* tがデータ型、dataか *)
           (match t with
            |TScalar ((TData (b',_, _)), _) when b' = data ->
              true
            |_ -> false)
         in
         let mk_match_case cons t =
           let cons_args: (Id.t * Type.t) list = type_args t in
           let cons_args = List.map (fun (id,t) -> Id.genid id, t) cons_args in
           let rec_args_type, nonrec_args_type =
             List.partition (fun (a,t) ->is_recursive_type t) cons_args
           in
           let rec_cons_args = List.map fst rec_args_type in
           let nonrec_cons_args = List.map fst nonrec_args_type in
           let nonrec_cons_args_term = List.map (fun i -> PSymbol i) nonrec_cons_args in
           let othere_args_term = List.map (fun i -> PSymbol i) othere_args in
           let g = gen_g_id () in
           let case_body =
             (if rec_cons_args = [] then
               Syntax.PHole
              else
                PE
                  (elist_2_e
                  (PAuxi g)
                  (nonrec_cons_args_term@othere_args_term@(List.map app_f rec_cons_args))))
             in
              {constructor = cons; argNames = List.map fst cons_args; body = case_body} in
         let data_info = M.find data data_info_map in
         let case_list = List.map
                           (fun (cons, (_,_,t)) -> mk_match_case cons t)
                           data_info.cons_list
         in
         let fun_body = PI (PMatch ((PSymbol x),case_list)) in
         let_rec f_name (List.map fst (type_args goal_t)) fun_body
         
       |None-> PHole
  )

(* split :: xs: RList a <{True}>->
   {Pair (RList a <{True}>) (RList a <{True}>) |
         len (fst _v)) == (len (snd _v) || (len (fst _v)) +1) == (len (snd _v)) &&
        (len (fst _v)) + (len (snd _v))) == (len xs)) &&
        (elems (fst _v) + elems (snd _v)) == elems xs  }	
 *)
  
(* let mk_split_schema (list, len, elem) (pair, fst, snd)  = *)
(*   let alpha = Id.genid "a" in   (\* type param *\) *)
(*   let p_len_fairness = *)
(*     (UF ( *)

let merge:  Data_info.t M.t ->  PreSyntax.measureInfo list ->
            Id.t -> Type.schema -> Syntax.t  =
  (fun data_info_map minfos f_name (_,_,goal_t)   ->
    (* data_info_map, minfosから、リスト,len,elemsを抽出する
    *)
    let (data_list: Data_info.t_list),
        (data_info_map: Data_info.t M.t),
        (minfos:PreSyntax.measureInfo list) =
      Data_info.extract_list data_info_map minfos
    in
    let (data_pair: Data_info.t_pair),
        (data_info_map: Data_info.t M.t),
        (minfos:PreSyntax.measureInfo list) =
      Data_info.extract_pair data_info_map minfos
    in
    match pop_data_type_arg goal_t with
    |Some ({name=l; nth=l_nth; data_id= data}, othere_args)
         when data = data_list.data_name -> (* list argument *)
         let app_f y =          (* fを再帰適用する項を作る *)
           let args = List.insert y l_nth othere_args in
           mk_fun_app_term (PSymbol f_name) args
         in
         let split =  "split" in
         let y = Id.genid "y" in
         let ys = Id.genid "ys" in
         let l1 = Id.genid "l1" in
         let l2 = Id.genid "l2" in
         let case_split =
           {constructor = data_list.cons;
            argNames =[y; ys];
            body =
              (PI
                 (PMatch ((PAppFo ((PSymbol split),(PSymbol l))),
                  [{constructor = data_pair.pair;
                    argNames = [l1; l2];
                    body =
                      (PE
                         (elist_2_e (PAuxi (gen_g_id () ))
                                    [(app_f l1); (app_f l2)]
                      ))
                  }])
                 )
              )
           }
         in
         let x = Id.genid "x"  in
         let xs = Id.genid "xs" in
         let  case_multi_elems =
           {constructor = data_list.cons;
            argNames = [x; xs];
            body =
              (PI
                 (PMatch ((PSymbol xs),
                          [{constructor = data_list.nil;
                            argNames = [];
                            body = PHole};
                           case_split
                          ]
                         )
                 )
              )
           }
         in
         let fun_body = 
           (PI
              (PMatch ((PSymbol l),
                       [{constructor = data_list.nil;
                         argNames = [];
                         body = PHole};
                        case_multi_elems
                       ]
                      )
              )
           )
         in
         let_rec f_name (List.map fst (type_args goal_t)) fun_body
    |_ ->
    
    PHole)


(* fundecs goalsに対し、mk_tmpでテンプレートを作成 
元々、ユーザで提供されてる場合はそのままにする*)
let f (mk_tmp: Id.t -> Type.schema ->  Syntax.t )
      (fundecs:(Id.t * Type.schema) list)
      (goals:(Id.t * Syntax.t) list) =
  List.map
    (fun (f_name, tmp) ->
      match tmp with
      |PHole ->
        let t = List.assoc f_name fundecs in
        (f_name, mk_tmp f_name t)
      |_ -> (f_name, tmp)
    )
    goals
  

      

