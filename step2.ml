open Syntax
open Type   



           
let rec constructor_shape c_t =
  match c_t with
  |TFun ((x,t1),t2) ->
    let args,ret = constructor_shape t2 in
    (x,t1)::args,ret
  |TScalar (b,p) ->[],p
  |_ -> assert false
      
let mk_constructor_arg_env (c_t:Type.t) {constructor = c_id;argNames = xs;body=_} =
  let c_t' = t_alpha_convert c_t xs in
  (* (Printf.printf "c_t:%s\nc_t':%s\n\n" (t2string c_t) (t2string c_t')); *)
  let args,ret = constructor_shape c_t' in
  let arg_env = List.map (fun (x,t) ->(x,mk_mono_schmea t)) args in
  (arg_env,[]),ret


(* e is a shpae of (auxi e1 e2 ...) *)
let rec extractConst z3_env data_infos qualifiers env e required_ty c =
  match e with
  |PAuxi i -> (i, Type.env_append env c, required_ty) 
  |PAppFo (e1, e2) ->
    let TLet (c_env1, ty2) = TypeInfer.fEterm  z3_env data_infos qualifiers env e2 in
    let y = Id.genid "y" in
    let required_ty_e1 = TFun ((y, ty2), required_ty) in 
    extractConst  z3_env data_infos qualifiers env e1 required_ty_e1 (env_append c_env1 c)
  |PAppHo (e1, f) ->
    
    let ty2 =TaSyntax.add_empty_annotation (PF f)
             |> TypeInfer.f  z3_env data_infos qualifiers env
    in
    let y = Id.genid "y" in
    let required_ty_e1 = TFun ((y, ty2), required_ty) in
    extractConst  z3_env data_infos qualifiers env e1 required_ty_e1 c
  |PSymbol _ -> assert false
              
    
  
  
let rec f' z3_env data_infos qualifiers (env:Type.env) (prg:Syntax.t) (t:Type.t) =
  match prg  with
  |PLet (x, t1, t2) ->
    let ty1 = TypeInfer.f  z3_env data_infos qualifiers env (TaSyntax.add_empty_annotation t1) in
    let env' = env_add env (x, ty1) in
    f'  z3_env data_infos qualifiers env' t2 t
  |PE e when auxi_exist e ->
    [extractConst  z3_env data_infos qualifiers env e t Type.env_empty ]

  |PE e -> []
         
  |PI (PIf (e, p1, p2)) ->
    (match TypeInfer.fEterm  z3_env data_infos qualifiers  env e  with
     |TLet(cenv, TScalar(TBool, p) ) ->
       let env' = Type.env_append cenv env in
       let np = Formula.Not p in
       let g_list1 = f'  z3_env data_infos qualifiers (Type.env_add_F env'  p) p1 t  in
       let g_list2 = f'  z3_env data_infos qualifiers (Type.env_add_F env' np) p2 t  in
       g_list1@g_list2
     |_ -> assert false)

  |PI (PMatch (e, cases) ) ->
    (match  TypeInfer.fEterm  z3_env data_infos qualifiers  env e  with
     |TLet(cenv, TScalar( TData (i, ts, ps),p )) ->
       print_string "go inside";
       let env_list =           (* 各ケースに対する環境を用意する。 *)
         List.map
           (fun case ->

             let z = Id.genid "z" in
             let ci_schema = env_find env case.constructor  in
             let ci_t = instantiate_implicit ci_schema ts ps in
             let ci_t = Type.t_alpha_convert ci_t case.argNames in
             let x_t_list, phi' = constructor_shape ci_t in
             let arg_env = Type.env_add_F
                             (Type.env_add_list  Type.env_empty  x_t_list)
                             (Formula.replace Id.valueVar_id z phi')
             in
             let env' = Type.env_add_F
                 (Type.env_append arg_env
                                 (Type.env_append cenv env))
                 (Formula.replace Id.valueVar_id z p)
             in
             env'
           )
           cases
       in
       List.fold_left2
         (fun acc env_i case ->
           let g_list = f' z3_env data_infos qualifiers env_i case.body t  in
           g_list@acc
         )
         []
         env_list
         cases
     |_ -> assert false)

  |PF f_e -> g_fun  z3_env data_infos qualifiers env f_e t 

  |PHole -> []

and g_fun  z3_env data_infos qualifiers env f_e t =
  match f_e with
    PFun (x,e) ->
    (match t with
     |TFun ((x',t1),t2) ->
       let t2' = replace_F x' x t2 in
       let env' = env_add env (x,t1) in
       f'  z3_env data_infos qualifiers env' e t2' 
     |_ ->assert false)
   |PFix (x,f_body) ->
     let env' = env_add env (x,t) in
     g_fun  z3_env data_infos qualifiers env' f_body t 

let rec f  z3_env data_infos qualifiers (env:Type.env) (prg:Syntax.t) ((ts,ps,t):Type.schema) =
  
  let ts_inst = List.map (fun i -> TScalar(TAny i,Formula.Bool true)) ts in
  let ps_inst = List.map (fun (r,shape) -> Formula.id2pa_shape r shape) ps in (* id *)
  let toplev_t = Type.instantiate_implicit (ts,ps,t) ts_inst ps_inst in
  (Printf.printf "\nafter instantiate:\n%s\n\n" (Type.t2string_sort toplev_t));
  match prg with
  |PF (PFix (f_name, PFun(x,e))) -> (* 再帰関数 *)
    (* let ts',ts_inst =List.split *)
    (*                    (List.map (fun i -> i, TScalar(TVar (M.empty,i),Formula.Bool true) ) *)
    (*                              (List.map Id.genid ts) ) *)
    (* in *)
    (* let ps',ps_inst =List.split *)
    (*                    (List.map (fun (r',shape) -> (r',shape), Formula.id2pa_shape r' shape) *)
    (*                              (List.map (fun (r,shape) ->(Id.genid r,shape)) ps)) *)
    (* in *)
    (* let t' = Type.instantiate_implicit (ts,ps,t) ts_inst ps_inst in *)
    (* let f_schema = (ts',ps',t') in *)
    let f_schema = (ts,ps,t) in    
    let env' = env_add_schema env (f_name, f_schema ) in (* 再帰関数登録 *)
    f'  z3_env data_infos qualifiers env' (PF (PFun(x,e))) toplev_t
  |PF (PFix (_, PFix _)) -> assert false
  |_ -> f'  z3_env data_infos qualifiers env prg toplev_t 

  
