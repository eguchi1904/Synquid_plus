type t =
  |TScalar of basetype * Formula.t
  |TFun of (Id.t * t) * t
  |TAny of Id.t                 (* a,b... トップレベルの型パラメタ、具体化しない*)
  |TBot                         (* ボトム型、型検査で補助的に利用 *)

 and basetype  =
   |TBool
   |TInt
   |TData of  Id.t * (t list) * ( Formula.pa list)  (* Di T <p> *)
   |TVar of Id.t

          
type schema =  (Id.t list) * ((Id.t * Formula.pa_shape) list) * t
(* type polymorphic predicate polymorphic *)
let mk_mono_schmea t :schema = ([],[],t)
(* contextual type *)


type subst = t M.t   (* 型変数の代入 *)

  
type env = (Id.t * schema) list * (Formula.t list)

type contextual = TLet of env * t
                        
type subtype_constrain = env * t * t (* env|= t1 <: t2 *)

let env_empty:env = ([],[])

let env_add ((l, p):env) ((x,t):Id.t * t) =
  ((x,([],[],t) )::l), p

let env_add_F ((l, ps):env)  (p:Formula.t) = (l, p::ps)

let env_find env v =
  match env with
    (l , p) -> List.assoc v l

let env_append ((its1, p1):env) ((its2, p2):env):env =
  (its1@its2, p1@p2)

    
(* freshな型変数で、 {a True} を返す *)
let genTvar s = TScalar (TVar (Id.genid s), (Formula.Bool true) )

(* Id.t型に対する、　{a true}を返す *)
let id2Tvar s =  TScalar (TVar  s, (Formula.Bool true) )

                           

exception InferErr of string
exception SubstErr of string

(* 型変数への代入 *)
let rec substitute_T (sita:subst) (t:t) =
  match t with
  |TScalar( TVar(v) , p  ) when M.mem v sita ->
    (match M.find v sita with
     |TScalar( b , p') ->
       if p' = Formula.Bool true then
         TScalar( b, p)
       else if p = Formula.Bool true then
         TScalar( b, p')
       else
         TScalar( b, (Formula.And(p',p) ) )
     |_ -> raise (SubstErr "type variable isnt scalar"))
  |TScalar( TData( i, ts, ps), p ) ->
    let ts' = List.map (substitute_T sita) ts in
    TScalar( TData( i, ts', ps), p )
  |TScalar _ -> t
  |TFun ((x,t1),t2) ->
    let t1' = substitute_T sita t1 in
    let t2' = substitute_T sita t2 in
    TFun ((x,t1'),t2')
  | _ -> t

(* 述語変数への代入 *)
let rec substitute_F (sita:Formula.subst) (t:t) =
  match t with
  |TScalar( TData( i, ts, ps), p ) ->
    let ts' = List.map (substitute_F sita ) ts in
    let ps' = List.map (fun (args,t) ->(args,Formula.substitution sita t)) ps in
    let p' =  Formula.substitution sita p in
    TScalar( TData (i, ts', ps'), p')
  |TScalar (b, p) ->
    let p' =  Formula.substitution sita p in
    TScalar (b, p')
  |TFun ((x,t1),t2) ->
    let t1' = substitute_F sita t1 in
    let t2' = substitute_F sita t2 in
    TFun ((x,t1'),t2')
  | _ -> t

let rec substitute_pa (pa_sita:Formula.pa M.t) (t:t) =
  match t with
  |TScalar (TData( i, ts, ps), p ) ->
    let ts' = List.map (substitute_pa pa_sita) ts in
    let ps' = List.map
                (* \x\y.r x y　の形のものを置き換える時に無駄がないように、、  *)
                (fun (arg,t) -> match Formula.eta_shape (arg,t) with
                           |Some r when M.mem r pa_sita -> M.find r pa_sita
                           |Some r -> (arg,t)
                           |None -> (arg,
                                     Formula.pa_substitution pa_sita t))
                ps
    in
    let p' = Formula.pa_substitution pa_sita p in
    TScalar (TData( i, ts',ps'),p')
  |TScalar (b, p) ->
    let p' = Formula.pa_substitution pa_sita p in
    TScalar (b,p')
  |TFun ((x,t1),t2) ->
    let t1' = substitute_pa pa_sita t1 in
    let t2' = substitute_pa pa_sita t2 in
    TFun ((x,t1'),t2')
  | _ -> t 
    
                    


let rec env_substitute_F (sita:Formula.subst) ((ts,ps):env) :env=
  let ts':(Id.t * schema) list =
    List.map (fun (x,(arg1,arg2,t)) -> (x, (arg1,arg2,substitute_F sita t))) ts
  in
  let ps' = List.map (Formula.substitution sita) ps in
  (ts',ps')
  
                         

(* 述語変数の置換 *)
let rec replace_F x y t =
  match t with
  |TScalar( TData( i, ts, ps), p ) ->
    let ts' = List.map (replace_F x y ) ts in
    let ps' = List.map (Formula.pa_replace x y) ps in
    let p' =  Formula.replace x y p in
    TScalar( TData (i, ts', ps'), p')
  |TScalar (b, p) ->
    let p' =  Formula.replace x y p in
    TScalar (b, p')
  |TFun ((x,t1),t2) ->
    let t1' = replace_F x y t1 in
    let t2' = replace_F x y t2 in
    TFun ((x,t1'),t2')
  | _ -> t
              

let instantiate ((ts,ps,t):schema) =
  let sita_t = List.fold_left
                 (fun sita i ->M.add i (genTvar "a") sita )
                 M.empty
                 ts
  in
  let sita_pa = List.fold_left
                 (fun sita (i,shape) ->M.add i (Formula.genUnknownPa_shape shape "p") sita)
                 M.empty
                 ps
in
(substitute_pa sita_pa ( substitute_T sita_t t) )

let instantiate_implicit ((ts,ps,t):schema) ts' ps' =
  let sita_t = List.fold_left2
                 (fun sita i t' ->M.add i t' sita)
                 M.empty
                 ts
                 ts'
  in
  let sita_pa = List.fold_left2
                  (fun sita (i,shape) pa' ->M.add i pa' sita)
                  M.empty
                  ps
                  ps'
  in
(substitute_pa sita_pa ( substitute_T sita_t t) )  
  

(* fに関係するenvの条件を抜き出す。 *)
let rec env2formula' (tenv:((Id.t*schema) list)) vset =
  match tenv with
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' -> (* schemaは無視して良いの? *)
    if S.mem x vset then
      (Formula.And ((Formula.replace (Id.valueVar_id) x p), (* [x/_v]p *)
                    (env2formula' tenv' (S.union (S.remove x vset) (Formula.fv p) ))
      ))
    else
      env2formula' tenv' vset

  |_ :: tenv' -> env2formula' tenv' vset

  |[] -> Formula.Bool true
    

let env2formula ((tenv,ps):env) (f:Formula.t) =
  let p = List.fold_right (fun p acc -> Formula.And (p,acc))
                          ps
                          (Formula.Bool true)
  in
  let tenv_p = env2formula' tenv (S.union (Formula.fv f) (Formula.fv p)) in
  Formula.And (tenv_p, p)
  
    

let rec gen_constrain env e t :contextual * (subtype_constrain list) * (env *t) option=
  match e with
  |Syntax.PSymbol i ->
    let (ts,ps,ti) = env_find env i in
    let ti' = instantiate (ts,ps,ti) in
    let constrain = (env, ti', t) in
    TLet (env_empty, ti'),[constrain], None
  |Syntax.PAuxi _ ->
    TLet (env_empty, t),[], Some (env, t)

  |Syntax.PAppFo (e1, e2) ->
    let (TLet(env2,t2), c2, _) = gen_constrain  env e2 TBot in
    let y = Id.genid "y" in
    let t1_req = TFun ((y, t2), t) in (* e1に要求する型 *)
    let (TLet(env1,t1), c1, gc) = gen_constrain (env_append env2 env) e1 t1_req in
    (match t1 with
     |TFun ((x, t1_in),t1_out) ->
       let env12 = env_append env1 env2 in
       let env' = env_append env env12 in
       let env' = env_add  env' (x, t2) in
       TLet (env', t1_out), (c1@c2), gc
     |_ -> raise (InferErr "not function type"))


let mk_constrain_pa env (args1, p1) (args2, p2) =
  (* まず、p2の引数をp1に合わせる。 *)
  let rec mk_subst args1 args2 =
    List.fold_left2
      (fun sita2 (i1,s1) (i2,s2) ->
        assert (s1 = s2);
        let input = Formula.Var (s1, i1) in
        let sita2' = M.add i2 input sita2 in
         sita2')
      M.empty
      args1
      args2
  in
  let sita2 =mk_subst args1 args2  in
  let p2' = Formula.substitution sita2 p2 in
  let env_f = env2formula env (Formula.And (p1 ,p2')) in
  (env_f, p1, p2')

    
let rec split (cs:subtype_constrain list) (tsubst:subst) =
  match cs with
  |(env, (TScalar (b1,p1) as t1), (TScalar (b2,p2) as t2))  :: left ->
    
    (match b1,b2 with
     |TVar a, _    when  M.mem a tsubst    ->
       let cs' = (env, M.find a tsubst, t2)::left in
       split cs' tsubst 
       
     |_ , TVar a   when M.mem a tsubst ->
       let cs' = (env, t1, M.find a tsubst)::left in
       split cs' tsubst

     |TVar a, TVar b ->
       assert (p1 = Formula.Bool true);
       assert (p2 = Formula.Bool true);
       if a = b then
         split left tsubst
       else
         let tsubst' = M.add a (id2Tvar b) tsubst in (* a=bという情報を加える,とりあえず近似 *)
         split left tsubst'
       
     |TVar a, TData (i2, ts2, ps2) ->
       let ts1 = List.map (fun _ -> genTvar a) ts2 in (* 新たな型変数 *)
       let ps1 = List.map (fun pa -> Formula.genUnknownPa pa a) ps2 in
       let refine = TScalar (TData (i2, ts1, ps1), Formula.Bool true) in
       let tsubst' = M.add a refine tsubst in
       let cs' = (env, refine,t2)::left in
       split cs' tsubst'

     |TData (i1, ts1, ps1), TVar a ->
       let ts2 = List.map (fun _ -> genTvar a) ts1 in (* 新たな型変数 *)
       let ps2 = List.map (fun pa -> Formula.genUnknownPa pa a) ps1 in
       let refine = TScalar (TData (i1, ts2, ps2), Formula.Bool true) in
       let tsubst' = M.add a refine tsubst in
       let cs' = (env, t1, refine)::left in
       split cs' tsubst'

     |TVar a, TBool ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TBool, p_a) in
       let tsubst' = M.add a refine tsubst in
       let cs' = (env, refine, t2) ::left in
       split cs' tsubst'

     |TBool, TVar a ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TBool, p_a) in
       let tsubst' = M.add a refine tsubst in
       let cs' = (env, t1, refine) ::left in
       split cs' tsubst'

     |TVar a, TInt ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TInt, p_a) in
       let tsubst' = M.add a refine tsubst in
       let cs' = (env, refine, t2) ::left in
       split cs' tsubst'

     |TInt, TVar a ->           (* 結果的に、env,p1 => p_a が出る。 *)
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TInt, p_a) in
       let tsubst' = M.add a refine tsubst in
       let cs' = (env, t1, refine) ::left in
       split cs' tsubst'       
               
     |TData (i1, ts1, ps1), TData (i2, ts2, ps2)  when i1 = i2->
       let ts1_ts2 = List.map2 (fun a b ->(env, a, b)) ts1 ts2 in
       let cs' = ts1_ts2@left in
       let cs_res, sub_res = split cs' tsubst in
       let ps1_ps2 = List.map2 (mk_constrain_pa env) ps1 ps2 in
       
       (ps1_ps2 @ cs_res), sub_res

     |TBool, TBool |TInt, TInt ->
       let cs_res, sub_res = split left tsubst in
       let env_p = env2formula env (Formula.Implies (p1, p2)) in
       ((env_p, p1, p2)::cs_res), sub_res

     |_ -> raise (InferErr "basetipe miss match")
    )

  |(env, (TFun ((x,t1),t2) ), (TFun ((x',t1'),t2')) )  :: left ->
    (* x:t1 -> t2 <: x':t1' -> t2' *)
    let env2 = env_add env (x',t1') in (* env;x':t1' *)
    let t2_rpl = replace_F x x' t2 in
    let cs' = (env2, t2_rpl, t2')      (* env; x':t1' |- [x'/x]t2 <: t2' *)
              ::((env, t1', t2')::left) in
    split cs' tsubst
   
  |(env, TAny i1, TAny i2) :: left when i1 = i2 ->  split left tsubst

  |(env, TBot, _) :: left -> split left tsubst

  |  _      :: left   -> raise (InferErr "type shape miss match")
                       
  |[] -> [], tsubst

       
let rec expand_tvar (tvar_map:subst) (t:t) =
  match t with
  |TScalar ((TVar i),p) when M.mem i tvar_map ->
    (assert (p = Formula.Bool true)); (* 型変数は、制約付きで現れない（わかりにくな） *)
    expand_tvar tvar_map (M.find i tvar_map)
  |TScalar ((TData (i, ts, ps)), p) ->
    let ts' = List.map (expand_tvar tvar_map) ts in
    TScalar ((TData (i, ts', ps)),p)
  |TScalar _ ->t

  |TFun ((x,t1), t2) ->
    TFun ((x, expand_tvar tvar_map t1), expand_tvar tvar_map t2)
  |_ -> t

let rec env_expand_tvar tvar_map ((ts,ps):env) :env=
  let ts' = List.map (fun (x,(ar1,ar2,t)) ->x,(ar1,ar2,expand_tvar tvar_map t)) ts in
  (ts',ps)

let rec contextual_expand_tvar tvar_map ((TLet (env,t)):contextual) =
  TLet ( (env_expand_tvar tvar_map env), expand_tvar tvar_map t)
                                        
  
  
  

let checkETerm env e t  z3_env =
  let contex_t,cs,g_t_op = gen_constrain env e t in
  match g_t_op with
  |None -> None
  |Some (g_env, g_t) ->
    let cs,tvar_map = split cs (M.empty) in
    let punknown_map = Find_unknownP.f cs z3_env in
    let g_t =  expand_tvar tvar_map g_t in
    let g_t' = substitute_F punknown_map g_t in
    let g_env' = env_substitute_F punknown_map g_env in
    Some (g_env', g_t')

let inferETerm env e z3_env = 
  let contex_t,cs,g_t_op = gen_constrain env e TBot in
  (assert (g_t_op = None));
   let cs,tvar_map = split cs (M.empty) in
   let punknown_map = Find_unknownP.f cs z3_env in
    let TLet (cenv, t) =  contextual_expand_tvar tvar_map contex_t in
    let t' = substitute_F punknown_map t in
    let cenv' = env_substitute_F punknown_map cenv in
    TLet(cenv', t')

  
    
