open Syntax
open Type   

let rec t_alpha_convert t ys =
  match ys with
  |[] -> t
  |y::ys' -> (match t with
              |TFun ((x,t1),t2) ->
                let t2' = replace_F x y t2 in (* [y/x]t2 *)
                TFun ((y,t1),(t_alpha_convert t2' ys'))
              |_ -> assert false)

           
let rec constructor_shape c_t =
  match c_t with
  |TFun ((x,t1),t2) ->
    let args,ret = constructor_shape t2 in
    (x,t1)::args,ret
  |TScalar (b,p) ->[],p
  |_ -> assert false
      
let mk_constructor_arg_env (c_t:Type.t) {constructor = c_id;argNames = xs;body=_} =
  let c_t' = t_alpha_convert c_t xs in
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
           (Printf.printf "%s\n" (t2string t));
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
   |PFix (x,f_name) ->
     let env' = env_add env (x,t) in
     g_fun env' f_name t z3_env

let rec f (env:Type.env) (prg:Syntax.t) ((ts,ps,t):Type.schema) z3_env=
  f' env prg t z3_env
  
