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

let rec f' (env:Type.env) (prg:Syntax.t) (t:Type.t) z3_env=
  match prg  with
  |PE e when auxi_exist e ->
    (match Type.checkETerm env e t z3_env with
     |Some (g_env, g_t) ->
       [(auxi_name e, g_env, g_t)]
     |None ->assert false)
  |PE e -> []
         
  |PI (PIf (e, p1, p2)) ->
    (match Type.inferETerm env e z3_env with
     |TLet(cenv, TScalar(TBool, p) ) ->
       let env' = Type.env_append cenv env in
       let np = Formula.Not p in
       let g_list1 = f' (Type.env_add_F env'  p) p1 t z3_env in
       let g_list2 = f' (Type.env_add_F env' np) p2 t z3_env in
       g_list1@g_list2
     |_ -> assert false)

  |PI (PMatch (e, cases) ) ->
    (match Type.inferETerm env e z3_env with
     |TLet(cenv, TScalar( TData (i, ts, ps),p )) ->
       print_string "go inside";
       let env_list =           (* 各ケースに対する環境を用意する。 *)
         List.map
           (fun case ->
             let z = Id.genid "z" in
             let ci_schema = env_find env case.constructor  in
             let ci_t = instantiate_implicit ci_schema ts ps in
             let arg_env,ret = mk_constructor_arg_env ci_t case in
             let ret' = Formula.replace Id.valueVar_id z ret in
             let p' = Formula.replace Id.valueVar_id z p in
             let env' = env_append cenv (env_append arg_env env) in
             let env' = env_add_F (env_add_F env' ret') p' in
             env'
           )
           cases
       in
       List.fold_left2
         (fun acc env_i case ->
           let g_list = f' env_i case.body t z3_env in
           g_list@acc
         )
         []
         env_list
         cases
     |_ -> assert false)

  |PF f_e -> g_fun env f_e t z3_env

  |PHole -> []

and g_fun env f_e t z3_env =
  match f_e with
    PFun (x,e) ->
    (match t with
     |TFun ((x',t1),t2) ->
       let t2' = replace_F x' x t2 in
       let env' = env_add env (x,t1) in
       f' env' e t2' z3_env
     |_ ->assert false)
   |PFix (x,f_body) ->
     let env' = env_add env (x,t) in
     g_fun env' f_body t z3_env

let rec f (env:Type.env) (prg:Syntax.t) ((ts,ps,t):Type.schema) z3_env=
  
  let ts_inst = List.map (fun i -> TScalar(TAny i,Formula.Bool true)) ts in
  let ps_inst = List.map (fun (r,shape) -> Formula.id2pa_shape r shape) ps in (* id *)
  let toplev_t = Type.instantiate_implicit (ts,ps,t) ts_inst ps_inst in
  (Printf.printf "\nafter instantiate:\n%s\n\n" (Type.t2string_sort toplev_t));
  match prg with
  |PF (PFix (f_name, PFun(x,e))) -> (* 再帰関数 *)
    let ts',ts_inst =List.split
                       (List.map (fun i -> i, TScalar(TVar (M.empty,i),Formula.Bool true) )
                                 (List.map Id.genid ts) )
    in
    let ps',ps_inst =List.split
                       (List.map (fun (r',shape) -> (r',shape), Formula.id2pa_shape r' shape)
                                 (List.map (fun (r,shape) ->(Id.genid r,shape)) ps))
    in
    let t' = Type.instantiate_implicit (ts,ps,t) ts_inst ps_inst in
    let f_schema = (ts',ps',t') in
    let env' = env_add_schema env (f_name, f_schema ) in (* 再帰関数登録 *)
    f' env' (PF (PFun(x,e))) toplev_t z3_env
  |PF (PFix (_, PFix _)) -> assert false
  |_ -> f' env prg toplev_t z3_env

  
