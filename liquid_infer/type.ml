open Extensions
   
type t =
  |TScalar of basetype * Formula.t
  |TFun of (Id.t * t) * t
  |TBot                         (* ボトム型、型検査で補助的に利用 *)

 and basetype  =
   |TBool
   |TInt
   |TData of  Id.t * (t list) * ( Formula.pa list)  (* Di T <p> *)
   |TVar of (Formula.subst) * Id.t                  (* will unuse *)
   |TAny of Id.t                
          

type schema =  (Id.t list) * ((Id.t * Formula.pa_shape) list) * t


             
let rec free_tvar' = function
  |TScalar (b,_) -> free_tvar_base b
  |TFun((x,t1), t2) -> (free_tvar' t1)@(free_tvar' t2) 
  |TBot -> []

and free_tvar_base = function
  |TAny  i -> [i]
  |TVar _ -> assert false
  |TData (_, ts, ps) ->
    List.concat (List.map free_tvar' ts)
  |TInt|TBool -> []

      
let free_tvar t =  List.uniq (free_tvar' t)




let rec t2string = function
  |TScalar (b,p) ->
    if p = Formula.Bool true then
      b2string b
    else
      Printf.sprintf "{%s | %s}" (b2string b) (Formula.p2string p)
  |TFun ((x,t1),t2) -> Printf.sprintf "(%s:%s -> %s)" x (t2string t1) (t2string t2)
  |TBot -> "Bot"

and b2string = function
  |TBool ->"Bool"|TInt -> "Int"
  |TData (i,ts,ps) ->
    let ts_string =
      List.map
        (fun t ->
          (match t with
           |TScalar ((TVar _), _) ->
             Printf.sprintf "%s" (t2string t) 
           |_ -> Printf.sprintf "(%s)" (t2string t)))
      ts
    in
    let ps_string_list = List.map Formula.pa2string ps in
    if ps = [] then
      Printf.sprintf "%s %s"
                     i
                     (String.concat " " ts_string)
    else
      Printf.sprintf "%s %s <{%s}> "
                     i
                     (String.concat " " ts_string)
                     (String.concat " " ps_string_list)
  |TVar (_,x) -> Printf.sprintf "%s" x
  |TAny a ->Printf.sprintf "%s" a


          
let rec t2string_sort = function
  |TScalar (b,p) ->

    Printf.sprintf "{%s | %s}"
                   (b2string_sort b)
                   (Formula.p2string_with_sort p)
   
  |TFun ((x,t1),t2) -> Printf.sprintf "%s:%s ->\n %s" x
                                      (t2string_sort t1)
                                      (t2string_sort t2)
  |TBot -> "Bot"

and b2string_sort = function
  |TBool ->"Bool"|TInt -> "Int"
  |TData (i,ts,ps) ->
    let ts_string = List.map t2string_sort ts in
    let ps_string_list = List.map Formula.pa2string ps in
    Printf.sprintf "%s %s <%s> "
                   i
                   (String.concat " " ts_string)
                   (String.concat " " ps_string_list)
  |TVar (_,x) -> Printf.sprintf "Var(%s)" x
  |TAny a ->Printf.sprintf "%s" a          


          
let rec b2sort  = function
  |TBool -> Some Formula.BoolS
  |TInt-> Some Formula.IntS
  |TData (i, ts,pas) ->
    let ts_sort_op  = List.map type2sort ts in
    if List.mem None ts_sort_op then
      None
    else
      let ts_sort = List.fold_right
                      (fun op acc ->match op with
                                    |None -> acc
                                    |Some s ->s::acc
                      )
                      ts_sort_op
                      []
      in
      Some (Formula.DataS (i,ts_sort))
  |TVar _ -> None
  |TAny a -> Some (Formula.AnyS a)
           
and type2sort = function
  |TScalar (b,p) -> b2sort b
  |_ -> None

let schema2sort ((_,_,ty) :schema) = type2sort ty

let rec sort2type sort = TScalar (sort2type_base sort, Formula.Bool true)
                                       
and sort2type_base = function
  |Formula.BoolS -> TBool
  |Formula.IntS -> TInt
  |Formula.DataS (i, sort_list) -> TData (i, (List.map sort2type sort_list), [])
  |Formula.AnyS i -> TAny i
  |Formula.SetS _|Formula.UnknownS _ -> raise (Invalid_argument "sort2type")

      

(* type polymorphic predicate polymorphic *)
let mk_mono_schmea t :schema = ([],[],t)
(* contextual type *)
let rec schema2string ((ts,ps,t):schema) =
  match ps with
  |(r,shape) :: left -> Printf.sprintf "<%s::%s>.%s"
                                       r
                                       (Formula.pashape2string shape)
                                       (schema2string (ts,left,t))
  |[] -> t2string t

type subst = t M.t   (* 型変数の代入 *)

           
type env = (Id.t * schema) list * (Formula.t list)

let rec env2string ((xts,ps):env) =
  let rec xts2string = function
    (* |(x,(_,_,t1))::( y, (_,_,t2) )::xts' -> *)
    (*   Printf.sprintf "%s:%s; %s:%s\n%s" x (t2string t1) y (t2string t2) (xts2string xts') *)
    |(x,sch)::xts' ->
      Printf.sprintf "%s :: %s\n%s" x (schema2string sch) (xts2string xts')
    |[] ->""
  in
  let rec ps2string = function
    |p::ps' ->
      Printf.sprintf "%s\n%s" (Formula.p2string p) (ps2string ps')
    |[] -> ""
  in
  Printf.sprintf
    "------------------------------------------------------------\
     \n%s\

     \n%s\
     \n============================================================\n"
    (xts2string xts)
    (ps2string ps)

type contextual = TLet of env * t
                        
type subtype_constrain = env * t * t (* env|= t1 <: t2 *)

let constrain2string ((env,t1,t2):subtype_constrain) =
  Printf.sprintf "%s%s\n<:\n%s\n"
                 (env2string env)
                 (t2string t1)
                 (t2string t2)

let constrain2string_F (p1,p2,p3) =
  Printf.sprintf
    "------------------------------------------------------------\
     \n%s\
     \n============================================================\
     \n%s\n==>\n%s\
     \n------------------------------------------------------------\n"
    (Formula.p2string p1)
    (Formula.p2string p2)
    (Formula.p2string p3)  

  
  
let env_empty:env = ([],[])

let env_add ((l, p):env) ((x,t):Id.t * t) =
  ((x,([],[],t) )::l), p

let env_add_list ((l, p):env) (xts: (Id.t * t) list) =
  let xschs = List.map (fun (x, t) -> (x, mk_mono_schmea t)) xts in
  (xschs@l, p)

let env_add_schema ((l,p):env) (x,s) =
  ((x,s)::l, p)

let env_add_F ((l, ps):env)  (p:Formula.t) = (l, p::ps)

let env_find env v =
  match env with
    (l , p) -> List.assoc v l

let env_append ((its1, p1):env) ((its2, p2):env):env =
  (its1@its2, p1@p2)

  
(* freshな型変数で、 {a True} を返す *)
let genTvar s = TScalar (TVar (M.empty,(Id.genid s)), (Formula.Bool true) )

(* Id.t型に対する、　{a true}を返す *)
let id2Tvar s =  TScalar (TVar (M.empty,s), (Formula.Bool true) )

let id2TAny s =  TScalar (TAny s, (Formula.Bool true) )

let rec mk_sort_env ((x_tys, _):env) = match x_tys with
  |(x, ty)::left ->
    (match schema2sort ty with
     |Some sort -> (x,sort)::(mk_sort_env (left,[]))
     |None -> mk_sort_env (left,[]))
  |[] -> []

  
               
exception InferErr of string
exception SubstErr of string



(* 述語変数への代入 *)
let rec substitute_F (sita:Formula.subst) (t:t) =
  match t with
  |TScalar( TVar(psubst,v), p) -> (* pending substitutionを合成 *)
    let psubst' = Formula.subst_compose sita psubst in
    let p' = Formula.substitution sita p in
    TScalar ( TVar(psubst',v), p')
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

(* 型変数への代入 *)
let rec substitute_T (sita:subst) (t:t) =
  match t with
  |TScalar( TAny v, p) when M.mem v sita ->
    let t' = M.find v sita in
    (match t' with
     |TScalar( b , p') ->
       if p' = Formula.Bool true then
         TScalar( b, p)
       else if p = Formula.Bool true then
         TScalar( b, p')
       else
         TScalar( b, (Formula.And(p',p) ) )
      
     |TFun _ -> t'              (* ignore p *)
     |_ -> (Printf.printf "formula:%s\n" (Formula.p2string p));assert false
    )
    
  |TScalar( TVar(psubst,v) , p  ) when M.mem v sita ->
    assert false
  |TScalar( TData( i, ts, ps), p ) ->
    let ts' = List.map (substitute_T sita) ts in
    TScalar( TData( i, ts', ps), p )
  |TScalar _ -> t
  |TFun ((x,t1),t2) ->
    let t1' = substitute_T sita t1 in
    let t2' = substitute_T sita t2 in
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
  
  

(* 述語変数の置換 [y/x]t x -> yに変換*)
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
  |TFun ((x',t1),t2) ->
    let t1' = replace_F x y t1 in
    let t2' = replace_F x y t2 in
    TFun ((x',t1'),t2')
  | _ -> t


(* sort の変数に代入するもの。preprocessのものの拡張 *)
(* 同じような関数を作っていて、汚い、 *)
let rec sort_subst2type sita (t:t) =
  match t with
  |TScalar( TData( i, ts, ps), p ) ->
    let ts' = List.map (sort_subst2type sita ) ts in
    let ps' = List.map
                (fun (args,t) ->
                  let args' =
                    List.map (fun (x, sort) -> (x, Formula.sort_subst sita sort)) args
                  in
                  (args',Formula.sort_subst2formula sita t))
                ps
    in
    let p' = Formula.sort_subst2formula sita p in
    TScalar( TData (i, ts', ps'), p')
    
  |TScalar (b, p) ->
    let p' =  Formula.sort_subst2formula sita p in
    TScalar (b, p')    

  |TFun ((x,t1),t2) ->
    let t1' = sort_subst2type sita t1 in
    let t2' = sort_subst2type sita t2 in
    TFun ((x,t1'),t2')
  | _ -> t



(*　explicit だった。。 *)
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
  let sita_sort = List.fold_left2
                    (fun sita i t' ->
                      match type2sort t' with
                      |Some sort' ->M.add i sort' sita
                      |None ->
                        (Printf.printf "instant to %s" (t2string t'));
                        sita)
                    M.empty
                    ts
                    ts'
  in
  ( sort_subst2type sita_sort
                    (substitute_pa sita_pa
                                   ( substitute_T sita_t t)))  
  

let instantiate ((ts,ps,t):schema) =
  let ts' = List.map genTvar ts in
  let ps' = List.map (fun (i, shape) -> Formula.genUnknownPa_shape shape i) ps in
  instantiate_implicit (ts,ps,t) ts' ps'
 
(* fに関係するenvの条件を抜き出す。 *)
(* let rec env2formula' (tenv:((Id.t*schema) list)) vset = *)
(*   match tenv with *)
(*   |(x, ([],[],(TScalar (b,p) ))) :: tenv' -> (\* schemaは無視して良いの? *\) *)
(*     if S.mem x vset then *)
(*       (Formula.And ((Formula.replace (Id.valueVar_id) x p), (\* [x/_v]p *\) *)
(*                     (env2formula' tenv' (S.union (S.remove x vset) (Formula.fv p) )) *)
(*       )) *)
(*     else *)
(*       env2formula' tenv' vset *)

(*   |_ :: tenv' -> env2formula' tenv' vset *)

(*   |[] -> Formula.Bool true *)

(* 環境全ての条件を抜き出すver *)
let rec env2formula' (tenv:((Id.t*schema) list)) vset =
  match tenv with
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' when p = Formula.Bool true-> (* schemaは無視して良いの? *)
    env2formula' tenv' S.empty  
   
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' -> (* schemaは無視して良いの? *)
    (Formula.And ((Formula.replace (Id.valueVar_id) x p), (* [x/_v]p *)
                  (env2formula' tenv' S.empty  )
    ))

  |_ :: tenv' -> env2formula' tenv' vset

  |[] -> Formula.Bool true       
       

let env2formula ((tenv,ps):env) free_v =
  let p = List.fold_right (fun p acc -> Formula.And (p,acc))
                          ps
                          (Formula.Bool true)
  in
  let tenv_p = env2formula' tenv (S.union free_v (Formula.fv p)) in
  Formula.And (tenv_p, p)

let rec mk_subst_for_const_var ((tenv, ps):env) =
  match tenv with
  |(x, ([],[], TScalar (b, Formula.Eq ( Formula.Var (_, v),
                                        Formula.Int i))))::left
   |(x, ([],[], TScalar (b, Formula.Eq ( Formula.Int i,
                                         Formula.Var (_, v) ))))::left
       when v = Id.valueVar_id
   ->
    M.add x (Formula.Int i) (mk_subst_for_const_var (left,ps))
   
  |(x, ([],[], TScalar (b, Formula.Eq ( Formula.Var (_, v),
                                        Formula.Bool tf))))::left
   |(x, ([],[], TScalar (b, Formula.Eq ( Formula.Bool tf,
                                         Formula.Var (_, v) ))))::left
       when v = Id.valueVar_id
   ->
    M.add x (Formula.Bool tf) (mk_subst_for_const_var (left,ps))

  |(x, ([],[], TScalar (b,  Formula.Var (_, v))))::left
       when v = Id.valueVar_id ->
    M.add x (Formula.Bool true) (mk_subst_for_const_var (left,ps))

  |(x, ([],[], TScalar (b,  (Formula.Not (Formula.Var (_, v))))))::left
       when v = Id.valueVar_id ->
    M.add x (Formula.Bool false) (mk_subst_for_const_var (left,ps))

  |_ ::left -> mk_subst_for_const_var (left,ps)

  |[] -> M.empty
                           
   
  
  
(* schemeを未知のVarで instantiate しながら、制約を作る。*)
let rec gen_constrain env e t :contextual * (subtype_constrain list) * (env *t) option=
  match e with
  |Syntax.PSymbol i ->
    (try
       (match env_find env i with
        |([],[],TScalar(b,_) ) ->
          (match b2sort b with
           |Some sort ->
             let ti' = TScalar(b,Formula.Eq (Formula.Var(sort,Id.valueVar_id),
                                             Formula.Var(sort,i)))
             in
             TLet(env_empty,ti'),
             [(env, ti', t)],                (* constrain *)
             None
           |None -> assert false)
        |(ts,ps,ti) ->
          let ti' = instantiate (ts,ps,ti) in
          let constrain = (env, ti', t) in
          TLet (env_empty, ti'),[constrain], None)
     with
       _ ->assert false)
  |Syntax.PAuxi _ ->
    TLet (env_empty, t),[], Some (env, t)

  |Syntax.PAppFo (e1, e2) ->
    let (TLet(env2,t2), c2, _) = gen_constrain  env e2 TBot in
    let y = Id.genid "y" in
    let t1_req = TFun ((y, t2), t) in (* e1に要求する型 *)
    let (TLet(env1,t1), c1, gc) = gen_constrain (env_append env2 env) e1 t1_req in
    (match t1 with
     |TFun ((x, t1_in),t1_out) ->
       (* 引数をフレッシュ *)
       let x' = Id.genid x in
       let t1_out' = replace_F x x' t1_out in (* [x'/x]t1_out *)
       
       let env12 = env_append env1 env2 in
       let env' = env_add  env12 (x', t2) in
       let constrain = (env_append env' env, t1_out', t) in
       TLet (env', t1_out'), (constrain::c1@c2), gc
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
  let env_f = env2formula env (Formula.fv (Formula.And (p1 ,p2'))) in
  (env_f, p1, p2')

  
let rec split (cs:subtype_constrain list) (tsubst:subst) =
  match cs with
  |(env, (TScalar (b1,p1) as t1), (TScalar (b2,p2) as t2))  :: left ->
    
    (match b1,b2 with
     |TVar (psubst,a), _    when  M.mem a tsubst    ->
       let t1' = substitute_F psubst (M.find a tsubst) in (* pending subst を展開 *)
       let cs' = (env, t1', t2)::left in
       split cs' tsubst 
       
     |_ , TVar (psubst, a)   when M.mem a tsubst ->
       let t2' = substitute_F psubst (M.find a tsubst) in (* pending subst を展開 *)
       let cs' = (env, t1, t2')::left in
       split cs' tsubst

     |TVar (psubst_a,a), TVar (psubst_b,b) -> (* 要検討 *)
       (if (p1 <> Formula.Bool true || p2 <> Formula.Bool true) then
         ((Printf.printf "\n%s vs %s\n" (t2string t1) (t2string t2)))
        else
          ());
       if a = b then
         split left tsubst
       else
         let tsubst' = M.add a (id2Tvar b) tsubst in (* a=bという情報を加える,とりあえず近似 *)
         split left tsubst'
           
     |TVar (psubst,a), TData (i2, ts2, ps2) ->
       let ts1 = List.map (fun _ -> genTvar a) ts2 in (* 新たな型変数 *)
       let ps1 = List.map (fun pa -> Formula.genUnknownPa pa a) ps2 in
       let refine = TScalar (TData (i2, ts1, ps1), Formula.Bool true) in
       let tsubst' = M.add a refine tsubst in 
       let refine' = substitute_F psubst refine in 
       let cs' = (env, refine',t2)::left in (* 制約にはpending substを展開したものを *)
       split cs' tsubst'

     |TData (i1, ts1, ps1), TVar (psubst,a) ->
       let ts2 = List.map (fun _ -> genTvar a) ts1 in (* 新たな型変数 *)
       let ps2 = List.map (fun pa -> Formula.genUnknownPa pa a) ps1 in
       let refine = TScalar (TData (i1, ts2, ps2), Formula.Bool true) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, t1, refine')::left in
       split cs' tsubst'

     |TVar (psubst,a), TBool ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TBool, p_a) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, refine', t2) ::left in
       split cs' tsubst'

     |TBool, TVar (psubst,a) ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TBool, p_a) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, t1, refine') ::left in
       split cs' tsubst'

     |TVar (psubst,a), TInt ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TInt, p_a) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, refine', t2) ::left in
       split cs' tsubst'

     |TInt, TVar (psubst,a) ->           (* 結果的に、env,p1 => p_a が出る。 *)
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TInt, p_a) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, t1, refine') ::left in
       split cs' tsubst'

     |TVar (psubst,a), TAny i ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TAny i, p_a) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, refine', t2) ::left in
       split cs' tsubst'

     |TAny i, TVar (psubst,a) ->
       let p_a = Formula.genUnkownP a in
       let refine = TScalar (TAny i, p_a) in
       let tsubst' = M.add a refine tsubst in
       let refine' = substitute_F psubst refine in
       let cs' = (env, t1, refine') ::left in
       split cs' tsubst'       
       
     |TData (i1, ts1, ps1), TData (i2, ts2, ps2)  when i1 = i2->
       let ts1_ts2 = List.map2 (fun a b ->(env, a, b)) ts1 ts2 in
       let cs' = ts1_ts2@left in
       let cs_res, sub_res = split cs' tsubst in
       let ps1_ps2 = List.map2 (mk_constrain_pa env) ps1 ps2 in
       
       (ps1_ps2 @ cs_res), sub_res

     |TBool, TBool |TInt, TInt ->
       let cs_res, sub_res = split left tsubst in
       let env_p = env2formula env (Formula.fv (Formula.Implies (p1, p2))) in
       ((env_p, p1, p2)::cs_res), sub_res

     |TAny i1, TAny i2 when i1 = i2 ->
       let cs_res, sub_res = split left tsubst in
       let env_p = env2formula env (Formula.fv (Formula.Implies (p1, p2))) in
       ((env_p, p1, p2)::cs_res), sub_res


     |_ -> raise (InferErr "basetipe miss match")
    )

  |(env, (TFun ((x,t1),t2) ), (TFun ((x',t1'),t2')) )  :: left ->
    (* x:t1 -> t2 <: x':t1' -> t2' *)
    let env2 = env_add env (x',t1') in (* env;x':t1' *)
    let t2_rpl = replace_F x x' t2 in
    let cs' = (env2, t2_rpl, t2')      (* env; x':t1' |- [x'/x]t2 <: t2' *)
              ::((env, t1', t1)::left) in
    split cs' tsubst
    
  |(env,_, TBot) :: left -> split left tsubst

  | (env,t1,t2)      :: left   ->
     let mes = Printf.sprintf
                 "type shape miss match\nt1\n%s\n\nt2\n%s\n" (t2string t1) (t2string t2)
     in

     raise (InferErr mes)
     
  |[] -> [], tsubst

       
let rec expand_tvar (tvar_map:subst) (t:t) =
  match t with
  |TScalar ((TVar (psubst,i),p)) when M.mem i tvar_map ->
    (match  substitute_F psubst (M.find i tvar_map) with
     |TScalar(b,p') as t' ->
       if p = Formula.Bool true then
         expand_tvar tvar_map t'
       else
         expand_tvar tvar_map (TScalar(b, Formula.And(p,p')))
     | _ -> assert false)
     (* let t' = substitute_F psubst (M.find i tvar_map) in *)
     (* expand_tvar tvar_map t' *)
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

(* constrainを求める（type vs type) list
   spilit で、constrainを分解し、論理式の制約を求める *)
let checkETerm env e t  z3_env =
  let contex_t,cs,g_t_op = gen_constrain env e t in
  
  (* let cs_string = List.map constrain2string cs in *)
  (* (List.iter (fun s -> Printf.printf "%s\n" s) cs_string); *)
  
  match g_t_op with
  |None -> None
  |Some (g_env, g_t) ->
    let cs,tvar_map = split cs (M.empty) in
    
    (* let cs_string = List.map constrain2string_F cs in *)
    (* (print_string "\n\nconstrain after split\n\n"); *)
    (* (List.iter (fun s -> Printf.printf "%s\n" s) cs_string); *)
    
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

  
(* 型の引数変数名を書き換え *)
let rec t_alpha_convert t ys =
  match ys with
  |[] -> t
  |y::ys' -> (match t with
              |TFun ((x,t1),t2) ->
                let t2' = replace_F x y t2 in (* [y/x]t2 *)
                TFun ((y,t1),(t_alpha_convert t2' ys'))
              |_ -> assert false)

let rec refresh_refinment t =
  match t with
  |TScalar (b,_) -> TScalar (b, Formula.Bool true)
  |TFun ((x,t1),t2) -> TFun ((x, refresh_refinment t1), refresh_refinment t2)
  |TBot -> TBot
  
        
