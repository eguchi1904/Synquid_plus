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

let rec positive_negative_unknown_p = function
  |TScalar (b, p) ->
    Formula.union_positive_negative_unknown_p_sets
      (positive_negative_unknown_p_base b)
      (Formula.positive_negative_unknown_p p)
  |TFun((x, t1), t2) ->
    let pos_ps1, neg_ps1, other_ps1 = positive_negative_unknown_p t1 in
    Formula.union_positive_negative_unknown_p_sets
      (neg_ps1, pos_ps1, other_ps1)
      (positive_negative_unknown_p t2)
  |TBot -> (S.empty, S.empty, S.empty)

and positive_negative_unknown_p_base = function
  |TAny _ -> (S.empty, S.empty, S.empty)
  |TVar _ -> assert false
  |TData (_, ts, ps) ->
    let pos_ts, neg_ts, othere_ts =
      List.fold_left
        (fun acc t -> Formula.union_positive_negative_unknown_p_sets
                        (positive_negative_unknown_p t)
                        acc
        )
        (S.empty, S.empty, S.empty)
        ts
    in
    let pos_ps, neg_ps, other_ps =
      List.fold_left
        (fun acc (arg,phi) -> Formula.union_positive_negative_unknown_p_sets
                                (Formula.positive_negative_unknown_p phi)
                                acc)
        (S.empty, S.empty, S.empty)
        ps
    in
    Formula.union_positive_negative_unknown_p_sets
      (pos_ts, neg_ts, othere_ts)
      (pos_ps, neg_ps, other_ps)
  |TInt|TBool -> (S.empty, S.empty, S.empty)
          

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
    let ps_string_list = List.map Formula.pa2string_detail ps in
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

let schema2ty ((_,_,t):schema) = t
(* contextual type *)
let rec schema2string ((ts,ps,t):schema) =
  match ps with
  |(r,shape) :: left -> Printf.sprintf "<%s::%s>.%s"
                                       r
                                       (Formula.pashape2string shape)
                                       (schema2string (ts,left,t))
  |[] -> t2string t


let rec schema2string_sort ((ts,ps,t):schema) =
  match ps with
  |(r,shape) :: left -> Printf.sprintf "<%s::%s>.%s"
                                       r
                                       (Formula.pashape2string shape)
                                       (schema2string (ts,left,t))
  |[] -> t2string_sort t
       
type subst = t M.t   (* 型変数の代入 *)


type envElm = |P of Formula.t | B of (Id.t * schema)
type env = envElm list

let rec env2string env =
  let rec emit_elm = function
    |(P p)::othere ->  Printf.sprintf "%s\n%s" (Formula.p2string p) (emit_elm othere)
    |(B (x,sch))::othere -> Printf.sprintf "%s :: %s\n%s" x (schema2string sch) (emit_elm othere)
    |[] -> ""
  in
  Printf.sprintf
    "------------------------------------------------------------\
     \n%s\
     \n============================================================\n"
    (emit_elm env)

type contextual = TLet of env * t

(* env manupulation *)
let env_empty:env = []

let env_add (env:env) ((x,t):Id.t * t) =
  (B (x,(mk_mono_schmea t)))::env

let env_add_list (env:env) (xts: (Id.t * t) list) =
  let xschs = List.map (fun (x, t) -> B (x, mk_mono_schmea t)) xts in
  (xschs@env)

let env_add_schema (env:env) (x,s) =
  (B (x,s))::env

let env_add_schema_list (env:env) sch_list =
  List.fold_right
    (fun (x,sch) acc_env -> (B (x,sch))::acc_env)
    sch_list
    env
  
  

let env_add_F (env:env)  (p:Formula.t) = (P p)::env

let rec env_find (env:env) v =
  match env with
  |(B (x,sch))::_ when x = v -> sch
  |_::othere -> env_find othere v
  |[] -> raise Not_found

let rec env_mem (env:env) v =
  match env with
  |(B (x,sch))::_ when x = v -> true
  |_::othere -> env_mem othere v
  |[] -> false

let env_append (dst_env:env) (env2:env):env =
  env2@dst_env

let env_fold f_b f_p env seed =
  List.fold_left
    (fun acc -> function
      |B x_sch -> f_b x_sch acc
      |P p -> f_p p acc)
    seed
    env

let env_pop (env:env) =
  match env with
  |x::xs -> xs
  |[] -> []
  
let env_fold_trace f_b f_p env seed =
  let acc, env = List.fold_left
                   (fun (acc, trace) -> function
                     |B x_sch -> (f_b trace x_sch acc, env_pop trace)
                     |P p -> (f_p trace p acc, env_pop trace))
                   (seed, env_pop env)
                   env
  in
  (assert( env = []));
  acc

let env_rev  = List.rev

(* env1のがでかい,envはデータ構造としては反転しているので *)
let env_suffix (env1:env) (env2:env) =
  let env1_rev = List.rev env1 in
  let env2_rev = List.rev env2 in  
  match List.suffix env1_rev env2_rev with
  |Some suffix_env_rev -> Some (List.rev suffix_env_rev)
  |None -> None

  
let env_bindings (env:env) =
  List.fold_right
    (fun env_elm acc ->
      match env_elm with
      |P _ -> acc
      |B (x,_) -> x::acc
    )
    env
    []


let env_extract_bindings (env:env) =
    List.fold_right
    (fun env_elm acc ->
      match env_elm with
      |P _ -> acc
      |B (x,sch) -> (x,sch)::acc
    )
    env
    []

  

let env_extract_unknown_p (env:env) =
  List.fold_left
    (fun acc -> function
      |P p -> S.union acc (Formula.extract_unknown_p p)
      |B (x, (_, pas, ty)) ->
        S.union acc (S.diff (extract_unknown_p ty)
                            (S.of_list (List.map fst pas))))
    S.empty
    env
  

let rec mk_sort_env (env:env) =
    List.fold_right
      (fun env_elm acc ->
        match env_elm with
        |P _ -> acc
        |B (x, sch) ->
          (match schema2sort  sch with
           |Some sort ->  Formula.Senv.add acc x sort
           |None -> acc)
      )
      env
  Formula.Senv.empty
         
               
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
       
       

(* 暗黙に、unknown predicate変数のvar変数に重なりがないことを過程している *)
let rec env_substitute_F (sita:Formula.subst) (env:env) :env=
    List.fold_right
      (fun env_elm acc ->
        match env_elm with
        |P p ->
          env_add_F acc (Formula.substitution sita p)
        |B (x, (arg1,arg2,ty)) ->
          env_add_schema acc (x,(arg1, arg2, substitute_F sita ty))
      )
      env
      env_empty


(* 環境の先頭から置換していく *)
let rec env_replace (replace_table:(Id.t * Formula.sort) M.t) (env:env) = 
  let env', _, _ = List.fold_right
                  (fun env_elm (acc, acc_replace_table, acc_subst) ->
                    match env_elm with
                    |P p -> (env_add_F acc (Formula.substitution acc_subst p)),
                            acc_replace_table,
                            acc_subst
                    |B (x, (arg1, arg2, ty)) when M.mem x acc_replace_table ->
                      let x', sort = M.find x acc_replace_table in
                      let acc_subst' = M.add x (Formula.Var (sort, x')) acc_subst in
                      (env_add_schema acc (x',(arg1, arg2, substitute_F acc_subst ty))),
                      M.remove x replace_table,
                      acc_subst'
                      
                    |B (x, (arg1, arg2, ty)) when M.mem x acc_subst -> (* これ以降のxには何もしない *)
                      let acc_subst' = M.remove x acc_subst in
                      (env_add_schema acc (x,(arg1, arg2, substitute_F acc_subst ty))),
                      acc_replace_table,
                      acc_subst'
                    |B (x, (arg1, arg2, ty)) ->
                      (env_add_schema acc (x,(arg1, arg2, substitute_F acc_subst ty))),
                      acc_replace_table,
                      acc_subst
                  )
                  env
                  (env_empty, replace_table, M.empty)
  in
  env'
        

  
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
                    ts'         (* instans先 *)
  in

  (substitute_pa sita_pa
                 ( substitute_T  sita_t
                                 ( sort_subst2type sita_sort   
                                                   t)))
  

let instantiate env ((ts,ps,t):schema) =
  let senv = mk_sort_env env in
  let t = alpha_fresh t in
  let ts' = List.map genTvar ts in
  let ps' = List.map (fun (i, shape) -> Formula.genUnknownPa_shape senv shape i) ps in
  instantiate_implicit (ts,ps,t) ts' ps'
 
let mk_valid x b =
  match b2sort b with
  |Some s ->  Formula.Eq (Formula.Var (s, x), Formula.Var (s, x))
  |None -> raise (Invalid_argument "mk_valid")
      

let rec env2formula' (env:env) free_v acc :Formula.t=
  match env with
  |B (x, ([],[],(TScalar (b,p)) )) :: othere when p = Formula.Bool true ->
    env2formula' othere free_v acc
  |B (x, ([],[],(TScalar (b,p)) )) :: othere when S.mem x free_v ->
    (match b2sort b with
       |Some x_sort ->
         let x_var = Formula.Var (x_sort, x) in
         let p_x = (Formula.substitution (M.singleton Id.valueVar_id x_var) p) in (* [x/_v]p *)
         let free_v' = S.union (S.remove x free_v) (Formula.fv p) in
         env2formula' othere free_v' (Formula.And (acc, p_x))
       |None -> invalid_arg "env2formula': free_v contain non-logical variable ")
   
  |B _ :: othere -> env2formula' othere free_v acc
                  
  |P p :: othere when (p = Formula.Bool true) ->
    env2formula' othere free_v acc
  |P p :: othere ->
    let free_v' = (S.union free_v (Formula.fv p)) in
    env2formula' othere free_v' (Formula.And (acc, p))
    
  |[] -> acc
      
         
let env2formula env free_v =  env2formula' env free_v (Formula.Bool true)
                            
(* 環境全ての条件を抜き出すver *)

let rec env2formula_all' (env:env) acc :Formula.t=
  match env with
  |B (x, ([],[],(TScalar (b,p)) )) :: othere when p = Formula.Bool true ->
    env2formula_all' othere  acc
  |B (x, ([],[],(TScalar (b,p)) )) :: othere ->
    (match b2sort b with
       |Some x_sort ->
         let x_var = Formula.Var (x_sort, x) in
         let p_x = (Formula.substitution (M.singleton Id.valueVar_id x_var) p) in (* [x/_v]p *)
         env2formula_all' othere  (Formula.And (acc, p_x))
       |None -> invalid_arg "env2formula_all': free_v contain non-logical variable ")
   
  |B _ :: othere -> env2formula_all' othere acc
                  
  |P p :: othere when (p = Formula.Bool true) ->
    env2formula_all' othere acc
  |P p :: othere ->
    env2formula_all' othere (Formula.And (acc, p))
  |[] -> acc
      
         
let env2formula_all env  = env2formula_all' env (Formula.Bool true)

  

let rec mk_subst_for_const_var (env:env) =
  match env with
  |B (x, ([],[], TScalar (b, Formula.Eq ( Formula.Var (_, v),
                                          Formula.Int i))))::left
   |B (x, ([],[], TScalar (b, Formula.Eq ( Formula.Int i,
                                         Formula.Var (_, v) ))))::left
       when v = Id.valueVar_id
   ->
    M.add x (Formula.Int i) (mk_subst_for_const_var left)
   
  |B (x, ([],[], TScalar (b, Formula.Eq ( Formula.Var (_, v),
                                        Formula.Bool tf))))::left
   |B (x, ([],[], TScalar (b, Formula.Eq ( Formula.Bool tf,
                                         Formula.Var (_, v) ))))::left
       when v = Id.valueVar_id
   ->
    M.add x (Formula.Bool tf) (mk_subst_for_const_var left)

  |B (x, ([],[], TScalar (b,  Formula.Var (_, v))))::left
       when v = Id.valueVar_id ->
    M.add x (Formula.Bool true) (mk_subst_for_const_var left)

  |B (x, ([],[], TScalar (b,  (Formula.Not (Formula.Var (_, v))))))::left
       when v = Id.valueVar_id ->
    M.add x (Formula.Bool false) (mk_subst_for_const_var left)

  |_ ::left -> mk_subst_for_const_var left

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
  


