open Formula
open Type
open PreSyntax
let sdummy = Formula.IntS

let rec sort_subst sita = function
  |AnyS i when M.mem i sita -> M.find i sita
  |UnknownS i when M.mem i sita -> M.find i sita
  |DataS (i, sortlist) ->DataS(i, List.map (sort_subst sita) sortlist )
  |SetS s -> SetS (sort_subst sita s)
  | s -> s

let rec sort_subst2formula sita = function
  |Set (s, ts) ->
    let ts' = List.map (sort_subst2formula sita) ts in
    Set (sort_subst sita s, ts')
  |Var (s,i) ->Var (sort_subst sita s, i)
  |Cons (s, i, ts) ->
    let ts' = List.map (sort_subst2formula sita) ts in
    Cons (sort_subst sita s, i, ts')
  |UF (s, i, ts) ->
    let ts' = List.map (sort_subst2formula sita) ts in
    UF (sort_subst sita s, i, ts')
                  
  (* 残りはただの再起 *)
  |All (is, t') ->All (is, (sort_subst2formula sita t'))
  |Exist (is, t') ->Exist (is, (sort_subst2formula sita t'))
  |If (t1, t2, t3) ->If ((sort_subst2formula sita t1),
                         (sort_subst2formula sita t2),
                         (sort_subst2formula sita t3))
  |Times (t1, t2) -> Times ((sort_subst2formula sita t1),
                            (sort_subst2formula sita t2))
  |Plus (t1, t2) -> Plus ((sort_subst2formula sita t1),
                          (sort_subst2formula sita t2))
  |Minus (t1, t2) -> Minus ((sort_subst2formula sita t1),
                            (sort_subst2formula sita t2))
  |Eq (t1, t2) -> Eq ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Neq (t1, t2) -> Neq ((sort_subst2formula sita t1),
                        (sort_subst2formula sita t2))
  |Lt (t1, t2) -> Lt ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Le (t1, t2) -> Le ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Gt (t1, t2) -> Gt ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Ge (t1, t2) -> Ge ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |And (t1, t2) -> And ((sort_subst2formula sita t1),
                        (sort_subst2formula sita t2))
  |Or (t1, t2) -> Or ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Implies (t1, t2) -> Implies ((sort_subst2formula sita t1),
                                (sort_subst2formula sita t2))
  |Iff (t1, t2) -> Iff ((sort_subst2formula sita t1),
                        (sort_subst2formula sita t2))
  |Union (t1, t2) -> Union ((sort_subst2formula sita t1),
                            (sort_subst2formula sita t2))
  |Intersect (t1, t2) -> Intersect ((sort_subst2formula sita t1),
                                    (sort_subst2formula sita t2))
  |Diff (t1, t2) -> Diff ((sort_subst2formula sita t1),
                          (sort_subst2formula sita t2))
  |Member (t1, t2) -> Member ((sort_subst2formula sita t1),
                              (sort_subst2formula sita t2))
  |Subset (t1, t2) -> Subset ((sort_subst2formula sita t1),
                              (sort_subst2formula sita t2))
  |Neg t1 -> Neg (sort_subst2formula sita t1)
  |Not t1 -> Not (sort_subst2formula sita t1)
  |t ->t 

(* let mk_unknown_sort i = AnyS (Printf.sprintf "unknown_%s" (Id.genid i)) *)
                      
(* let is_unknown_sort s = *)
(*   match s with *)
(*   |AnyS i -> *)
(*     if String.length i >7 then *)
(*       (String.sub i 0 7) = "unknown" *)
(*     else *)
(*       false *)
(*   |_ -> false *)


let rec sort_anyids = function
  |AnyS i  -> S.singleton i
  |DataS (i, sortlist) ->
    let anyids_list = List.map sort_anyids sortlist in
    List.fold_left (fun acc ids -> S.union acc ids) S.empty anyids_list
  |SetS s -> sort_anyids s
  |BoolS|IntS -> S.empty
  |UnknownS _ -> assert false

(* Any a と Unkown a' で　a != a' *)
(* ソートs中のAny a を　Unknown a' に変換する *)
let rec any2unknownsort s =
  let any_ids = sort_anyids s in
  let sita = S.fold
               (fun any_id sita -> M.add any_id (UnknownS (Id.genid any_id)) sita)
               any_ids
               M.empty
  in
  sort_subst sita s

let rec any2unknownsort_pa (args,rets) =
  let any_args =
    List.fold_left
      (fun acc set -> S.union set acc)
      S.empty
      (List.map sort_anyids args)
  in
  let any_ids = S.union any_args (sort_anyids rets) in
  let sita = S.fold
               (fun any_id sita -> M.add any_id (UnknownS (Id.genid any_id)) sita)
               any_ids
               M.empty
  in
  let args' = List.map (sort_subst sita) args in
  let rets' = sort_subst sita rets in
  (args', rets')
           

           
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

         


(* 単一化で、使う。ソート中のunknown な変数を他のソートで代入する。 *)
(* sort_substがあるのでいらない気がしてきた(追記） *)
let rec subst_unknown_sort s1 s2 target_sort=
  match target_sort with
  |BoolS |IntS -> target_sort
  |DataS (id, slist) -> DataS (id, (List.map (subst_unknown_sort s1 s2) slist))
  |SetS s' -> subst_unknown_sort s1 s2 s'
  |UnknownS id when id = s1 -> s2
  |s -> s

let compose_sort_subst (sita1:sort M.t) (sita2:sort M.t) = (* sita t = sita1(sita2 t) *)
  let sita2' = M.mapi
                 (fun i t ->
                   sort_subst sita1 t)
                 sita2         
  in
  M.union (fun i t1 t2 -> Some t2) sita1 sita2'      
(* unknown ソートに関する代入を作成する。 *)
let rec unify_sort constrain sita =
  match constrain with

  |((UnknownS a), sort2):: c  ->
    let sita' = compose_sort_subst (M.singleton a sort2) sita in
    let c' = List.map           (* 制約全体に代入[sort2/a]c *)
               (fun (c1,c2)-> (subst_unknown_sort a sort2 c1,
                               subst_unknown_sort a sort2 c2))
               c
    in
    unify_sort c' sita'
    
  |(sort2, (UnknownS a)) :: c ->
    let sita' = compose_sort_subst (M.singleton a sort2) sita in
    let c' = List.map           (* 制約全体に代入[sort2/a]c *)
               (fun (c1,c2)-> (subst_unknown_sort a sort2 c1,
                               subst_unknown_sort a sort2 c2))
               c
    in
    unify_sort c' sita'
                                                    
  |(DataS (i, sorts1), (DataS (i', sorts2))) :: c  when i = i' ->
    let new_c = (List.map2 (fun a b ->(a,b)) sorts1 sorts2)@c in
    unify_sort new_c sita

  |((SetS s1),(SetS s2)) :: c ->
    let new_c = (s1,s2) :: c in
    unify_sort new_c sita

  |(s1,s2) :: c when s1 = s2 -> unify_sort c sita

  |[] -> sita

  |(s1,s2) :: c ->
    (Printf.printf "%s vs %s" (sort2string s1) (sort2string s2));
    assert false




(* 返還後の式と constrainを返す。
空リストのソートとかを決定するためにconstrainが必要。
また、measure等のソート
len: List a -> Int 
などの,各出現に対するaを具体化するためにもconstrainが必要。
一旦、aをunknown_aに変換する。 *)
let rec fillsort' senv senv_param senv_var = function
  |Bool b -> Bool b, (BoolS, [])
  |Int i-> Int i, (IntS, [])
  |Set (_,[]) ->let unknown_s = UnknownS (Id.genid "emps") in
                Set (unknown_s,[]), (SetS ( unknown_s), [])
  |Set (_,es) ->
    let es', sort_constrain =
      List.split (List.map (fillsort' senv senv_param senv_var) es) in
    let (s1::sorts),constrainlist = List.split sort_constrain in
    let constrain = List.concat constrainlist in
    let new_c = List.map (fun s -> (s1,s)) sorts in (* 各elemが同じ *)
    Set (s1, es'), (SetS s1, new_c@constrain)

  |Var (_, i) when List.mem_assoc i senv_var->
    Var (List.assoc i senv_var, i), (List.assoc i senv_var, [])

  |Unknown _ -> assert false

  |Cons (_, i, []) when List.mem_assoc i senv->
    let (argsort, rets) = List.assoc i senv in
    let rets' = any2unknownsort rets in
    Cons (rets', i, []), (rets', [])
              
  |Cons (_, i, es) when List.mem_assoc i senv->
    let es', sort_constrain = List.split (List.map (fillsort' senv senv_param senv_var) es) in
    let es_sorts, constrainlist = List.split sort_constrain in
    let constrain = List.concat constrainlist in
    let (argsort, rets) = any2unknownsort_pa (List.assoc i senv) in
    let new_c = List.map2 (fun a b ->(a,b)) es_sorts argsort in
    Cons (rets, i, es'), (rets, new_c@constrain)

  |UF (_, i, es)  when List.mem_assoc i senv -> (* measureの適用 *)
    let es', sort_constrain = List.split (List.map (fillsort' senv senv_param senv_var) es) in
    let es_sorts, constrainlist = List.split sort_constrain in
    let constrain = List.concat constrainlist in
    let (argsort, rets) = any2unknownsort_pa (List.assoc i senv) in
    (Printf.printf "\n\ninstans measure:%s as %s\n\n" i (pashape2string (argsort, rets)));
    let new_c = List.map2 (fun a b ->(a,b)) es_sorts argsort in
    UF (rets, i, es'), (rets, new_c@constrain)

  |UF (sort, i, es) when List.mem_assoc i senv_param -> (* abstract refinmet *)
    let es',sorts_constrain = List.split (List.map (fillsort' senv senv_param senv_var) es) in
    let es_sorts, constrainlist = List.split sorts_constrain in
    let constrain = List.concat constrainlist in    
    let (argsort, rets) = List.assoc i senv_param in (* anyはそのまま *)
    let new_c = List.map2 (fun a b ->(a,b)) es_sorts argsort in
    UF (rets, i, es'), (rets, new_c@constrain)

  |If (e1,e2,e3) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let e3',(s3,c3) = fillsort' senv senv_param senv_var e3 in
    let new_c = [(s1,BoolS);(s2,s3)] in
    If (e1', e2', e3'), (s2, new_c@c1@c2@c3)

  |Times (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    (match s1 with 
    |IntS -> Times (e1',e2'), (IntS, consrain')
     |SetS s -> Intersect (e1',e2'), (SetS s, consrain')
     |_ -> assert false)
    
  |Plus (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    (match s1 with
     |IntS -> Plus (e1',e2'), (IntS, consrain')
     |SetS s -> Union (e1',e2'), (SetS s, consrain')
     |_ -> assert false)

  |Minus (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    (match s1 with
     |IntS -> Minus (e1',e2'), (IntS, consrain')
     |SetS s -> Diff (e1',e2'), (SetS s, consrain')
     |_ -> assert false)

  |Eq (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Eq (e1', e2'), (BoolS, consrain')

  |Neq (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Neq (e1', e2'), (BoolS, consrain')

  |Lt (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Lt (e1', e2'), (BoolS, consrain')

  |Le (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    (match s1 with
     |SetS s -> Subset (e1',e2'), (BoolS, consrain')
     |_ -> Le (e1',e2'), (BoolS,consrain')
    )

  |Gt (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Gt (e1', e2'), (BoolS, consrain')

  |Ge (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(c1@c2) in
    Ge (e1', e2'), (BoolS, consrain')

  |And (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    And (e1', e2'), (BoolS, consrain')

  |Or (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    Or (e1', e2'), (BoolS, consrain')

  |Implies (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    Implies (e1', e2'), (BoolS, consrain')

  |Iff (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (s1,s2)::(s1,BoolS)::(c1@c2) in
    Iff (e1', e2'), (BoolS, consrain')

  |Member (e1, e2) ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let e2',(s2,c2) = fillsort' senv senv_param senv_var e2 in
    let consrain' = (SetS s1,s2)::(c1@c2) in
    Member (e1', e2'), (BoolS, consrain')

  |Neg e1 ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let consrain' = (s1,IntS)::c1 in
    Neg e1', (IntS, consrain')

  |Not e1 ->
    let e1',(s1,c1) = fillsort' senv senv_param senv_var e1 in
    let consrain' = (s1,BoolS)::c1 in
    Not e1', (BoolS, consrain')

  |Union _ | Intersect _ | Diff _ |Subset _ -> (* 構文解析時には、int演算に変換される *)
    assert false

  |e ->(Printf.printf "%s\n" (Formula.p2string e) );
       assert false

(* fillsort' によって、 Unknown sort が含まれる式e'とconstrainが返される
 constrainを解き、e'中のUnknown sortを適切に置き換える  *)
let print_sort_constrain cs =
  let cs_str =
    String.concat
      "; "
      (List.map (fun (c1,c2) -> Printf.sprintf "(%s,%s)"
                                              (Formula.sort2string c1)
                                              (Formula.sort2string c2))
                cs)
  in
  Printf.printf "\n\nwe will solve ...\n%s\n\n" cs_str

let print_sort_subst sita =
  M.iter (fun i sort -> Printf.printf "%s -> %s\n" i (Formula.sort2string sort)) sita
  
let fillsort senv senv_param senv_var e =
  let (e',(_,constrain)) = fillsort' senv senv_param senv_var e in
  (* (print_sort_constrain constrain ); *)
  let sita = unify_sort constrain M.empty in (* unifyは適切か *)
  (* (print_sort_subst sita); *)
  sort_subst2formula sita e'                 (* 代入は適切か *)

let fillsort2pa senv senv_param senv_var (pa:pa) =
  match pa with
  |([(r,_)],_) when List.mem_assoc r senv_param -> (* 省略記法だった場合に対応 *)
    let r_shape = List.assoc r senv_param in
    id2pa_shape r r_shape
    
  |(args,e) ->
    let e' = fillsort senv senv_param (args@senv_var) e in
    (args, e')
    
let rec fillsort2type  senv senv_param senv_var =function
  |TScalar (b,p) ->
    let vs = base2pashape b in
    let senv_var' = (Id.valueVar_id, vs) :: senv_var in
    let p'= fillsort senv senv_param senv_var' p in
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
  |(_,p) ->                  (* pの中で、_0,_1が引数 *)
    let args' = List.mapi (fun i s ->(Printf.sprintf "_%d" i),s) arg_sort in
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
  (Printf.printf "env\n%s\n\n" (Type.env2string (env',[])));
  let fundecs' = fillsort2env senv fundecs' in
  (env', fundecs')
  
  
  
  
