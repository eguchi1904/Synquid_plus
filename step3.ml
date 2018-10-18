open Type
open Formula

let mk_all argv env p =
  let env_f = env2formula env (S.union argv (Formula.fv p)) in
  let bv = fv_sort' (And (env_f, p)) in
  let bv = List.filter (fun (x,s) -> not (S.mem x argv)) bv in
  let env_f_list = list_and env_f in
  QAll (bv, env_f_list, p)

let mk_exist argv env p = 
  let env_f = env2formula env  (S.union argv (Formula.fv p)) in
  let bv = fv_sort' (And (env_f, p)) in
  let bv = List.filter (fun (x,s) -> not (S.mem x argv)) bv in
  let env_f_list = list_and env_f in
  QExist (bv, p::env_f_list)
   
let necess_pa argv env ((arg,p):pa) =
  let pa' = genUnknownPa (arg,p) "P" in
  let argv' = S.union argv (S.of_list (List.map fst arg) ) in (* argも全称化対象外 *)
  match pa' with
  |arg,Unknown(_,_,p_i) ->
    (pa',[p_i, (mk_all argv' env p)])
  |_ -> assert false
    
let suff_pa argv env ((arg,p):pa) =
  let pa' = genUnknownPa (arg,p) "P" in
  let argv' = S.union argv (S.of_list (List.map fst arg) ) in (* argも全称化対象外 *)  
  match pa' with
  |arg,Unknown( _,_,p_i) ->
    (pa',[p_i, (mk_exist argv' env p)])
  |_ -> assert false

let rec necess_type (argv:S.t) env t =
  let argv_str = String.concat "," (S.elements argv) in
  (Printf.printf "\nnecess_args:arg=[%s]\n%s %s\n\n\n" argv_str (env2string env) (t2string t));
  match t with
  |TScalar( TData (i, ts, pas), p) ->
    let ts',p_map1s = List.split (List.map (necess_type argv env) ts) in
    let pas',p_map2s = List.split (List.map (necess_pa argv env) pas) in
    let p_map1 = List.concat p_map1s in
    let p_map2 = List.concat p_map2s in
    let p_i = Id.genid "P" in
    let p_map = (p_i, mk_all argv env p)::(p_map2 @ p_map1) in
    TScalar( TData (i, ts', pas'), Unknown (M.empty, M.empty, p_i)), p_map

  |TScalar( b, p) ->
    let p_i = Id.genid "P" in
    let p_map = [(p_i, mk_all argv env p)] in
    TScalar(b, Unknown (M.empty, M.empty, p_i)), p_map
    
  |TFun ((x,t1), t2) ->
    let t1',p_map1 = suff_type argv env t1 in
    let t2',p_map2 = necess_type (S.add x argv) (env_add env (x,t1)) t2 in
    TFun ((x,t1'), t2'), p_map2@p_map1

  |TBot -> assert false

and suff_type argv env t = 
  match t with
  |TScalar( TData (i, ts, pas), p) ->
    let ts',p_map1s = List.split (List.map (suff_type argv env) ts) in
    let pas',p_map2s = List.split (List.map (suff_pa argv env) pas) in
    let p_map1 = List.concat p_map1s in
    let p_map2 = List.concat p_map2s in
    let p_i = Id.genid "P" in
    let p_map = (p_i, mk_exist argv env p)::(p_map2 @ p_map1) in
    TScalar( TData (i, ts', pas'), Unknown (M.empty, M.empty, p_i)), p_map
    
  |TScalar( b, p) ->
    let p_i = Id.genid "P" in
    let p_map = [(p_i, mk_exist argv env p)] in
    TScalar(b, Unknown (M.empty, M.empty, p_i)), p_map
    
  |TFun ((x,t1), t2) ->
    let t1',p_map1 = necess_type argv env t1 in
    let t2',p_map2 = suff_type (S.add x argv) (env_add env (x,t1)) t2 in
    TFun ((x,t1'), t2'), p_map2@p_map1

  |TBot -> assert false

let f g_name env t =
  let t', p_map = necess_type S.empty env t in
  let p_map' = List.map (fun (p_i,p) ->(p_i, Qe.f p )) p_map in
  let sita = List.fold_left (fun sita (p_i,p) ->M.add p_i p sita) M.empty p_map' in
  substitute_F sita t'
  
  
                  
  
