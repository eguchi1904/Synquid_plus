open Formula
open Type
open PreSyntax
let sdummy = Formula.IntS

let rec sort_subst sita = function
  |AnyS i when M.mem i sita -> M.find i sita
  |AnyS i -> assert false
  |DataS (i, sortlist) ->DataS(i, List.map (sort_subst sita) sortlist )
  |SetS s -> SetS (sort_subst sita s)
  | s -> s

           
let rec t_args c_t =
  match c_t with
  |Type.TFun((x,t1), t2) -> x :: t_args t2
  |_ -> []

let rec add_formula2return e t =
  match t with
  |TFun((x,t1), t2) ->
    let t2' = add_formula2return e t2 in
    TFun((x,t1), t2')
  |TScalar (b,e1) ->
    let e' = And (e1, e) in
    TScalar (b, e')
  |TBot -> assert false

let add_measure env  m_name {constructor = cons; args = xs; body = e } =
  let (ts,ps,c_type) = List.assoc cons env in
  let v = Var ( sdummy, Id.valueVar_id ) in
  let xs' = t_args c_type in
  let sita = List.fold_left2
               (fun sita x x' -> M.add x (Var (sdummy, x')) sita)
               M.empty
               xs
               xs'
  in
  let e' = Formula.substitution sita e in
  let e' = Eq ( UF(sdummy, m_name, [v]), e') in (*  e.g. len _v = len xs + 1  *)
  let c_type' = add_formula2return e' c_type in
  let env' = List.remove_assoc cons env in
  (cons, (ts,ps,c_type') )::env'



let measure_info2env env ((m_name, (m_shape, cases)):measureInfo) =
  let env' = List.fold_left
               (fun env case ->add_measure env m_name case)
               env
               cases
  in
  env'

let minfos2env env minfos :(Id.t * Type.schema) list =
  List.fold_left measure_info2env env minfos


(* constructorの型から、述語としてのsortを作る。　＊型は一階 *)
let rec base2pashape = function
  |TBool -> BoolS
  |TInt -> IntS
  |TData (i, ts, _) ->
    let sortlist = List.map
                     (fun t -> match type2pashape t with
                               |([],rets) ->rets
                               |_ -> assert false)
                     ts
    in
    DataS (i, sortlist)
  |TVar (_,i) -> AnyS i
  |_ -> assert false

and type2pashape = function
  |TScalar (b,_) -> ([], base2pashape b)
  |TFun ((x,t1), t2) ->
    (match type2pashape t1 with
     |([], s) -> let (arg, rets) = type2pashape t2 in
                 (s::arg, rets)
     | _ -> assert false)
  |TBot -> assert false

(* sortlist1 = sortlist2 となるような、sortlist1への代入を求める。 *)
let rec unify_sort sortlist1 sortlist2 sita =
  match (sortlist1, sortlist2) with

  |(AnyS a):: left1, sort2:: left2 when M.mem a sita ->
    (assert ((M.find a sita) = sort2 ));
    unify_sort left1 left2 sita
    
  |(AnyS a):: left1, sort2:: left2 ->
    let sita' = M.add a sort2 sita in
    unify_sort left1 left2 sita'

  |BoolS::left1',BoolS::left2'
   |IntS::left1',IntS::left2'  ->  unify_sort left1' left2' sita
                                                    
  |(DataS (i, sorts1) :: left1), (DataS (i', sorts2) :: left2)
       when i = i' ->
    let sita' =unify_sort sorts1 sorts2 sita in
    unify_sort left1 left2 sita'

  |(SetS s1)::left1, (SetS s2)::left2 ->
    let sita' = unify_sort [s1] [s2] sita in
    unify_sort left1 left2 sita'

  |[],[] -> sita

  |_ -> assert false

          
  
let rec fillsort senv senv_param senv_var = function
  |Bool b -> Bool b, BoolS
  |Int i-> Int i, IntS
  |Set (_,es) ->
    let es', sorts = List.split (List.map (fillsort senv senv_param senv_var) es) in
    let elmsort = List.hd sorts in
    Set (elmsort, es'), SetS elmsort

  |Var (_, i) when List.mem_assoc i senv_var->
    Var (List.assoc i senv_var, i), List.assoc i senv_var

  |Unknown _ -> assert false
              
  |Cons (_, i, es) when List.mem_assoc i senv->
    let es', sorts = List.split (List.map (fillsort senv senv_param senv_var) es) in
    let (argsort, rets) = List.assoc i senv in
    let sita = unify_sort argsort sorts M.empty in (* argsortをsortsに合わせる代入を得る *)
    let rets' = sort_subst sita rets in
    Cons (rets', i, es'), rets'

  |UF (_, i, es)  when List.mem_assoc i senv -> (* measureの適用 *)
    let es', sorts = List.split (List.map (fillsort senv senv_param senv_var) es) in
    let (argsort, rets) = List.assoc i senv in
    let sita = unify_sort argsort sorts M.empty in (* argsortをsortsに合わせる代入を得る *)
    let rets' = sort_subst sita rets in
    UF (rets', i, es'), rets'

  |UF (sort, i, es) when List.mem_assoc i senv_param -> (* abstract refinmet *)
    let es', sorts = List.split (List.map (fillsort senv senv_param senv_var) es) in
    let (argsort, rets) = List.assoc i senv_param in
    (Printf.printf "%s" (Formula.p2string (UF (sort, i, es))));
    (assert (sorts = argsort) );
    UF (rets, i, es'), rets

  |If (e1,e2,e3) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    let e3',s3 = fillsort senv senv_param senv_var e3 in
    assert (s1 = BoolS);
    assert (s2 = s3);
    If (e1', e2', e3'), s2

  |Times (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    (match s1 with
     |IntS -> Times (e1',e2'), IntS
     |SetS s -> Intersect (e1',e2'), SetS s
     |_ -> assert false)
    
  |Plus (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    (match s1 with
     |IntS -> Plus (e1',e2'), IntS
     |SetS s -> Union (e1',e2'), SetS s
     |_ -> assert false)

  |Minus (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    (match s1 with
     |IntS -> Minus (e1',e2'), IntS
     |SetS s -> Diff (e1',e2'), SetS s
     |_ -> assert false)

  |Eq (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Eq (e1', e2'), BoolS

  |Neq (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Neq (e1', e2'), BoolS

  |Lt (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Lt (e1', e2'), BoolS

  |Le (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    (match s1 with
     |IntS -> Le (e1',e2'), BoolS
     |SetS s -> Subset (e1',e2'), BoolS
     |_ -> assert false)

  |Gt (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Gt (e1', e2'), BoolS

  |Ge (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Ge (e1', e2'), BoolS

  |And (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    And (e1', e2'), BoolS

  |Or (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Or (e1', e2'), BoolS

  |Implies (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Implies (e1', e2'), BoolS

  |Iff (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    assert (s1 = s2);
    Iff (e1', e2'), BoolS

  |Member (e1, e2) ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    let e2',s2 = fillsort senv senv_param senv_var e2 in
    Member (e1', e2'), BoolS

  |Neg e1 ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    assert (s1 = IntS);
    Neg e1', IntS

  |Not e1 ->
    let e1',s1 = fillsort senv senv_param senv_var e1 in
    assert (s1 = BoolS);
    Not e1', BoolS

  |Union _ | Intersect _ | Diff _ |Subset _ -> (* 構文解析時には、int演算に変換される *)
    assert false

  |e ->(Printf.printf "%s\n" (Formula.p2string e) );
       assert false

let fillsort2pa senv senv_param senv_var (pa:pa) =
  match pa with
  |([(r,_)],_) when List.mem_assoc r senv_param -> (* 省略記法だった場合に対応 *)
    let r_shape = List.assoc r senv_param in
    id2pa_shape r r_shape
    
  |(args,e) ->
    let e',_ = fillsort senv senv_param (args@senv_var) e in
    (args, e')
    
let rec fillsort2type  senv senv_param senv_var =function
  |TScalar (b,p) ->
    let vs = base2pashape b in
    let senv_var' = (Id.valueVar_id, vs) :: senv_var in
    let p',_ = fillsort senv senv_param senv_var' p in
    let b' = fillsort2basetype senv senv_param senv_var b in
    TScalar (b', p')
  |TFun ((x,t1),t2) ->
    (match type2pashape t1 with
     |([],t1_sort) ->
       let t1' = fillsort2type senv senv_param senv_var t1 in
       let t2' = fillsort2type senv senv_param ((x,t1_sort)::senv_var) t2 in
       TFun ((x,t1'), t2')
     |_ -> assert false)
  |_ -> assert false

and fillsort2basetype senv senv_param senv_var = function
  |TData (i, ts, ps) ->
    let ts' = List.map (fillsort2type senv senv_param senv_var) ts in
    let ps' = List.map (fillsort2pa senv senv_param senv_var) ps in
    TData (i, ts', ps')

  |b -> b

let rec fillsort2schema  senv ((ts,ps,t):schema) :schema=
  let t' = fillsort2type senv ps [] t in
  (ts,ps,t')
  

let rec fillsort2env senv (env:(Id.t * schema) list) =
  List.map (fun (x,schm) ->(x, fillsort2schema senv schm) ) env



let rec fill_pa_args ((arg_sort,rets):(Formula.pa_shape)) senv_param (pa:pa) =
  match pa with
  |([(r,_)],_) when List.mem_assoc r senv_param ->
    let r_shape = List.assoc r senv_param in
    id2pa_shape r r_shape
  |(args,p) ->
    let args' = List.map2 (fun (i,_) s ->(i,s)) args arg_sort in
    (args', p)
  

let rec fill_pa_args2type (data_pas:(Id.t * (Formula.pa_shape list)) list) senv_param t =
  match t with
  |TScalar (TData (i, ts, ps), p) when List.mem_assoc i data_pas ->
    let shapes :(Formula.pa_shape list) = List.assoc i data_pas in
    let ps' = List.map2 (fun  shape pa -> fill_pa_args shape senv_param pa) shapes ps in
    let ts' = List.map (fill_pa_args2type data_pas senv_param) ts in
    TScalar (TData (i, ts', ps'), p)

  |TScalar (TData (i, ts, ps), p) ->  assert false

  |TFun ((x,t1), t2) ->
    let t1' = fill_pa_args2type data_pas senv_param t1 in
    let t2' = fill_pa_args2type data_pas senv_param t2 in
    TFun ((x,t1'), t2')

  |t -> t

let rec fill_pa_args2schema data_pas ((ts,ps,t):schema) =
  let t' = fill_pa_args2type data_pas ps t in
  (ts,ps,t')

let rec fill_pa_args2env data_pas (env:(Id.t * schema) list) =
  List.map (fun (x,schm) ->(x, fill_pa_args2schema data_pas schm)) env

let rec which_data_cons = function
  |TScalar (TData(i, _,_), _) ->i
  |TFun ((x,t1), t2) -> which_data_cons t2
  |_ -> assert false
  
let rec mk_data_pas (env:(Id.t * schema) list) =
  List.fold_left
    (fun data_pas (i, (ts,ps,t)) ->
      let data_id = which_data_cons t in
      if List.mem_assoc data_id data_pas then
        data_pas
      else
        let shape_list = List.map snd ps in
        (data_id, shape_list) :: data_pas
    )
    []
    env
        
(* まず、envにはコンストラクタが入っている。 *)
let f env minfos fundecs =
  let senv_cons = List.map (fun (cons,(_,_,c_t)) -> (cons, type2pashape c_t) ) env in
  let senv_mes = List.map (fun (mes, (shape,_)) -> (mes, shape)) minfos in
  let senv = senv_cons@senv_mes in
  let env = minfos2env env minfos in (*  measrureの情報を追加 *)

  let data_pas = mk_data_pas env in
  let env' = fill_pa_args2env data_pas env in
  let fundecs' = fill_pa_args2env data_pas fundecs in
  
  let env' = fillsort2env senv env' in
  let fundecs' = fillsort2env senv fundecs' in
  (env', fundecs')
  
  
  
  
