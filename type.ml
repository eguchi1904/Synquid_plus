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


  
(* freshな型変数で、 {a True} を返す *)
let genTvar s = TScalar (TVar (M.empty,(Id.genid s)), (Formula.Bool true) )

(* Id.t型に対する、　{a true}を返す *)
let id2Tvar s =  TScalar (TVar (M.empty,s), (Formula.Bool true) )

let id2TAny s =  TScalar (TAny s, (Formula.Bool true) )
                 


let rec extract_unknown_p = function
  |TScalar (b, p) -> S.union (extract_unknown_p_base b) (Formula.extract_unknown_p p)
  |TFun((x,t1), t2) -> S.union (extract_unknown_p t1) (extract_unknown_p t2) 
  |TBot -> S.empty

and extract_unknown_p_base = function
  |TAny  i -> S.empty
  |TVar _ -> assert false
  |TData (_, ts, ps) ->
    let ts_set =
      List.fold_left
        (fun acc t -> S.union (extract_unknown_p t) acc)
        S.empty
        ts
    in
    let ps_set =
      List.fold_left
        (fun acc (_, body) -> S.union (Formula.extract_unknown_p body) acc)
        S.empty
        ps
    in
    S.union ts_set ps_set
  |TInt|TBool -> S.empty

          


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

(* env manupulation *)
let env_empty:env = ([],[])

let env_add ((l, p):env) ((x,t):Id.t * t) =
  ((x,([],[],t) )::l), p

let env_add_list ((l, p):env) (xts: (Id.t * t) list) =
  let xschs = List.map (fun (x, t) -> (x, mk_mono_schmea t)) xts in
  (xschs@l, p)

let env_add_schema ((l,p):env) (x,s) =
  ((x,s)::l, p)

let env_add_schema_list ((l,p):env) shc_list =((shc_list@l, p))
  

let env_add_F ((l, ps):env)  (p:Formula.t) = (l, p::ps)

let env_find env v =
  match env with
    (l , p) -> List.assoc v l

let env_mem env v =
  match env with
    (l , p) -> List.mem_assoc v l             

let env_append ((its1, p1):env) ((its2, p2):env):env =
  (its1@its2, p1@p2)


  
let env_bindings (env,_) =
  List.map fst env

let env_extract_bindings (env,_) = env

let env_extract_unknown_p ((l, p):env) =
  let l_unknown_p_set =
    List.fold_left
      (fun acc (_, (_, pas, ty)) ->
        S.union
          (S.diff (extract_unknown_p ty)
                  (S.of_list (List.map fst pas)))
          acc)
      S.empty
      l
  in
  S.union
    l_unknown_p_set
    (Formula.extract_unknown_p (Formula.and_list p))

let rec mk_sort_env ((x_tys, _):env) = match x_tys with
  |(x, ty)::left ->
    (match schema2sort ty with
     |Some sort -> (x,sort)::(mk_sort_env (left,[]))
     |None -> mk_sort_env (left,[]))
  |[] -> []

  
               
(* -------------------------------------------------- *)
(* substitution *)
(* -------------------------------------------------- *)        

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


let rec alpha_fresh = function
  |TFun ((x, ty1), ty2) ->
    let new_x = Id.genid x in
    let x_sort = (match type2sort ty1 with Some s -> s| _ -> assert false) in
    let new_x_var = Formula.Var (x_sort, new_x) in
    let new_ty2 = substitute_F (M.singleton x new_x_var) ty2 in
    TFun ((new_x, alpha_fresh ty1),
          (alpha_fresh new_ty2))
  |TScalar _ | TBot as ty -> ty

(*　explicit だった。。


  x:a -> {a | }
 a -> {int | _v > x}
などとそのままinstantiateすると、
xが衝突することに注意

 *)
let instantiate_implicit ((ts,ps,t):schema) ts' ps' =
  let t = alpha_fresh t in
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

  (substitute_pa sita_pa
                 ( substitute_T  sita_t
                                 ( sort_subst2type sita_sort   
                                                   t)))
  

let instantiate ((ts,ps,t):schema) =
  let t = alpha_fresh t in
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
let mk_valid x b =
  match b2sort b with
  |Some s ->  Formula.Eq (Formula.Var (s, x), Formula.Var (s, x))
  |None -> raise (Invalid_argument "mk_valid")
(* _v = vを追加するver *)
(* let rec env2formula' (tenv:((Id.t*schema) list)) vset = *)
(*   match tenv with *)
(*   |(x, ([],[],(TScalar (b,p) ))) :: tenv' when p = Formula.Bool true-> (\* schemaは無視して良いの? *\) *)
(*     (Formula.And ((mk_valid x b),  *)
(*      (env2formula' tenv' vset))) *)
   
(*   |(x, ([],[],(TScalar (b,p) ))) :: tenv' -> (\* schemaは無視して良いの? *\) *)
(*     if S.mem x vset then *)
(*       (if S.mem Id.valueVar_id (Formula.fv p) *)
(*         then *)
(*           (Formula.And ((Formula.replace (Id.valueVar_id) x p), (\* [x/_v]p *\) *)
(*                         (env2formula' tenv' (S.union (S.remove x vset) (Formula.fv p)  )) *)
(*           )) *)
(*        else *)
(*          Formula.And ((mk_valid x b), (Formula.And (p, (env2formula' tenv' (S.union (S.remove x vset) (Formula.fv p)))))) *)
(*       ) *)
(*     else *)
(*       env2formula' tenv' vset *)

(*   |_ :: tenv' -> env2formula' tenv' vset *)

(*   |[] -> Formula.Bool true *)

       
let rec env2formula' (tenv:((Id.t*schema) list)) vset =
  match tenv with
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' when p = Formula.Bool true-> (* schemaは無視して良いの? *)
    env2formula' tenv' vset
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' -> (* schemaは無視して良いの? *)
    if S.mem x vset then
      match b2sort b with
      |Some x_sort ->
        let x_var = Formula.Var (x_sort, x) in
        (Formula.And ((Formula.substitution (M.singleton Id.valueVar_id x_var) p), (* [x/_v]p *)
                        (env2formula' tenv' (S.union (S.remove x vset) (Formula.fv p)  ))
        ))
      |None ->assert false (* env2formula' tenv' vset *)
    else
      env2formula' tenv' vset

  |_ :: tenv' -> env2formula' tenv' vset

  |[] -> Formula.Bool true          

let env2formula ((tenv,ps):env) free_v =
  let p = List.fold_right (fun p acc -> Formula.And (p,acc))
                          ps
                          (Formula.Bool true)
  in
  let tenv_p = env2formula' tenv (S.union free_v (Formula.fv p)) in
  Formula.And (tenv_p, p)

(* 環境全ての条件を抜き出すver *)
let rec env2formula_all' (tenv:((Id.t*schema) list))  =
  match tenv with
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' when p = Formula.Bool true-> (* schemaは無視して良いの? *)
    env2formula_all' tenv' 
   
  |(x, ([],[],(TScalar (b,p) ))) :: tenv' -> (* schemaは無視して良いの? *)
    (match b2sort b with
     |Some x_sort ->
       let x_var = Formula.Var (x_sort, x) in    
       (Formula.And ((Formula.substitution (M.singleton Id.valueVar_id x_var) p), (* [x/_v]p *)
                     (env2formula_all' tenv'   )
    ))
     |None -> assert false
    )

  |_ :: tenv' -> env2formula_all' tenv' 

  |[] -> Formula.Bool true
       
  

let env2formula_all  ((tenv,ps):env) =
  let p = List.fold_right (fun p acc -> Formula.And (p,acc))
                          ps
                          (Formula.Bool true)
  in
  let tenv_p = env2formula_all' tenv  in
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
                           
   
  
  
(* 型の引数変数名を書き換え *)
let rec t_alpha_convert t ys =
  match ys with
  |[] -> t
  |y::ys' -> (match t with
              |TFun ((x,t1),t2) ->
                let x_sort = (match type2sort t1 with Some s -> s |None -> assert false) in
                let y_var = Formula.Var (x_sort, y) in
                let t2' = substitute_F (M.singleton x y_var) t2 in (* [y/x]t2 *)
                TFun ((y,t1),(t_alpha_convert t2' ys'))
              |_ -> assert false)

let rec refresh_refinment t =
  match t with
  |TScalar (b,_) -> TScalar (b, Formula.Bool true)
  |TFun ((x,t1),t2) -> TFun ((x, refresh_refinment t1), refresh_refinment t2)
  |TBot -> TBot
  
        
