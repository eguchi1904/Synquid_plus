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
   
let fold: Id.t -> Type.schema -> Syntax.t -> ((Id.t * Type.schema) list) M.t -> Syntax.t =
  (fun f_name (_,_,goal_t) tmp data_cons_list ->
    match tmp with
    |PHole ->                   (* when there *)
      (match pop_data_type_arg goal_t with
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
             elist_2_e
               (PAuxi g)
               (nonrec_cons_args_term@othere_args_term@(List.map app_f rec_cons_args)) in
           {constructor = cons; argNames = List.map fst cons_args; body =PE case_body}
         in
         let cons_schema_list = M.find data data_cons_list in
         let case_list = List.map
                           (fun (cons, (_,_,t)) -> mk_match_case cons t)
                           cons_schema_list
         in
         let fun_body = PI (PMatch ((PSymbol x),case_list)) in
         let_rec f_name (List.map fst (type_args goal_t)) fun_body
         
         |None-> tmp)
  
      
    |_ -> tmp)
 
