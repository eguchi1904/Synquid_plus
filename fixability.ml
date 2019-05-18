open Extensions
   
module Liq = Type
module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
            
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority

module PFixState = PredicateFixState

module PFixableConstraintCounter = PredicateFixableCounter

module CFixState = ConstraintFixState

                 

(* constraint中の、pの位置を保持する:　   \gamma;p;\delata |- e1 -> e2 etc *)
type pPosition =
  |Positive of {env: Liq.env
               ;negFormula: Formula.t
                              (*  p is here *)
               }
  |Negative of {backEnv: Liq.env
               (*  p is here *)                 
               ;frontEnv: Liq.env 
               ;posFormula:Formula.t}

type bound =
  (* env|- \phi -> p *)
  |LowBound of {localEnv: Liq.env
               ;vars: S.t
               ;require: Formula.t (* no unknown p in boud *)
               }
  (* env|- p -> \phi *)
  (* env;p;delta'|- \phi1 -> \phi2 *)
  |UpBound of {localEnv: Liq.env
              ;vars: S.t
              ;require: (Liq.env * Formula.t) (* no unknown p in bound *)
              }

let string_of_bound = function
  |LowBound rc ->
    "Low -> "^(Formula.p2string rc.require)
  |UpBound rc ->
    "Up <- "^(Formula.p2string (snd rc.require))
   
let unknown_in_localEnv assign = function
  |LowBound {localEnv = local_env} |UpBound {localEnv = local_env} ->
    S.filter
      (fun x ->not (M.mem x assign))
      (Liq.env_extract_unknown_p local_env)

   

let predicate_polarity_of_bound = function
  |LowBound _ -> Polarity.pos
  |UpBound _ -> Polarity.neg
              

let extract_necessary_predicate senv unknown env =
  Liq.env_fold
    (fun (x,sch) (acc_unknown, acc_p) ->
      if  (S.mem x acc_unknown) then
        match sch with
        |([], [], Liq.TScalar (_, phi)) ->
          let phi_fv = (Formula.fv phi) in (* = fv ([_v->x].phi) / {x}  *)
          let new_unknown' = S.filter (fun x -> not (Formula.Senv.mem x senv)) phi_fv  in
          let acc_unknown' = S.union new_unknown' acc_unknown in
          let acc_p' = S.union acc_p (Formula.extract_unknown_p phi) in
          (acc_unknown', acc_p')
        | _ -> (acc_unknown, acc_p)
      else
        (acc_unknown, acc_p)
    )    
    (fun phi (acc_unknown, acc_p) ->
      let phi_fv = (Formula.fv_include_v phi) in
      if S.is_empty (S.inter  phi_fv acc_unknown) then
        (acc_unknown, acc_p)
      else
        let new_unknown' = S.filter (fun x -> not (Formula.Senv.mem x senv)) phi_fv  in
        let acc_unknown' = S.union new_unknown' acc_unknown in
        let acc_p' = S.union acc_p (Formula.extract_unknown_p phi) in
        (acc_unknown', acc_p')
    )
    env
    (unknown, S.empty)


let rec iter_extract_necessary_predicate senv unknown env =
  let unknown', necess_p = extract_necessary_predicate senv unknown env in
  let () = assert ((S.cardinal unknown) <= (S.cardinal unknown')) in
  if S.equal unknown' unknown then
    necess_p
  else
    let () = assert ((S.cardinal unknown) < (S.cardinal unknown')) in
    iter_extract_necessary_predicate senv unknown' env
  
  
let wait_predicates assign senv = function
  |LowBound {localEnv = local_env; vars = vars; require = _}
   |UpBound {localEnv = local_env; vars = vars; require = _ } ->
    let local_env' = Liq.env_substitute_F assign local_env in
    iter_extract_necessary_predicate senv vars local_env'


let rec extract_subst senv acc_sita eq_list =
  let open Formula in
  match List.pop
          (function |(x, Var (_,y)) -> not (Senv.mem y senv)
                    | _ -> false)
          eq_list
  with
  |Some ((x, Var (sort, y)), eq_list') ->
    let y2x = M.singleton y (Var (sort, x)) in
    let eq_list' = List.map (fun (x,e) -> (x, substitution y2x e)) eq_list' in
    extract_subst senv (subst_compose y2x acc_sita) eq_list'
  |Some _ -> assert false     (* popの条件から *)
  |None -> acc_sita, eq_list

         
let mk_fresing_subst senv sita =
  M.fold
    (fun x _ acc ->
      let x_sort = try Formula.Senv.find x senv with _ -> assert false in
      let x' = Id.genid x in
      M.add x (Formula.Var (x_sort, x')) acc)
    sita  
    M.empty

  

let mk_replace_table sita =
  M.map
    (function |Formula.Var (sort, x) -> (x, sort)
              |_ -> invalid_arg "mk_replace_table: not varible to varialbe substitution"
    )
  sita
  
  
let mk_flatten_subst senv sita =
  let sita_debug = M.bindings sita in
  let freshing_sita = mk_fresing_subst senv sita in
  let freshing_sita_debug = M.bindings freshing_sita in  
  let eq_list =
    M.bindings sita
    |> List.map (fun (x, e) -> (x, Formula.substitution freshing_sita e))
  in
  let delta, eq_list' = extract_subst senv M.empty eq_list in
  let delta_debug = M.bindings delta in
  let eq_phi = eq_list'
               |> List.map
                    (fun (x,e) ->
                      let x_sort = try Formula.Senv.find x senv with _ -> assert false in
                      Formula.Eq (Formula.Var (x_sort, x), e))
               |> Formula.and_list
  in
  Formula.subst_compose delta freshing_sita
  , eq_phi

let extract_argument_vars senv env =
  Formula.Senv.reveal senv
  |> List.filter (fun (x,_) -> not (Liq.env_mem env x))
  |> List.map fst
  |> S.of_list
  
(* let extract_argument_vars senv env = *)
(*   let () =  Format.eprintf "go to extartct@" in *)
(*   let ret = extract_argument_vars senv env  in *)
(*   let () = assert false in *)
(*   ret *)
  

(* envはpが定義されたところでの環境 *)
let mk_bound assign senv env pending_sita = function
  |Positive {env = cons_env; negFormula = e1 } ->
    (match Liq.env_suffix cons_env env with
     |None -> invalid_arg "Solver.mk_bound: cons_env and env mismatch"
     |Some local_env ->
       let flatten_sita, eq_phi = mk_flatten_subst senv pending_sita in
       let flatten_replace = mk_replace_table flatten_sita in
       let local_env' = Liq.env_substitute_F assign local_env (* ここはやらなくても良い *)
                        |>Liq.env_replace flatten_replace     (* envの変数をreplaceするための関数 *)
       in
       let e1' = Formula.substitution assign e1 
                 |>Formula.substitution flatten_sita
       in
       let require = Formula.And (e1', eq_phi) in
       let unknown_vars = S.filter (fun x -> not (Formula.Senv.mem x senv))

                                   (Formula.fv require)
       in
       (* let env' = Liq.env_replace flatten_replace env in *)
       let vars = if S.is_empty unknown_vars then unknown_vars
                  else
                    S.union
                      unknown_vars
                      (extract_argument_vars senv env) (* 引数変数を関係しているものとして加える *)
       in
       LowBound {localEnv = local_env'
                ;vars = vars
                ;require = require}
    )
  |Negative {backEnv = cons_back_env
            ;frontEnv = cons_front_env
            ;posFormula = e1} ->
    (match Liq.env_suffix cons_back_env env with
     |None ->                   (* error *)
       let () = print_string
                  ("cons_back_env:\n"
                ^(Liq.env2string cons_back_env)
                ^"env:^\n"
                ^(Liq.env2string env))
       in
       invalid_arg "Solver.mk_bound: cons_env and env mismatch"
     |Some local_env ->
       let flatten_sita, eq_phi = mk_flatten_subst senv pending_sita in
       let pending_sita_debug = M.bindings pending_sita in
       let flatten_replace = mk_replace_table flatten_sita in       
       let flatten_sita_debug = M.bindings flatten_sita in
       let local_env' = Liq.env_substitute_F assign local_env (* ここはやらなくても良い *)
                        |>Liq.env_replace flatten_replace
       in
       let e1' = Formula.substitution assign e1 
                 |>Formula.substitution flatten_sita
       in
       let cons_front_env' = Liq.env_substitute_F assign cons_front_env
                             |>Liq.env_substitute_F flatten_sita
       in
       let require_env = Liq.env_add_F cons_front_env' eq_phi in
       let require = (require_env, e1') in
       let require_fv = Liq.env2formula_all require_env
                        |> Formula.fv_include_v
                        |>S.union (Formula.fv_include_v e1')
       in
       let unknown_vars = S.filter (fun x -> not (Formula.Senv.mem x senv))
                           require_fv
       in
       (* let env' = Liq.env_replace flatten_replace env in *)
       let vars = if S.is_empty unknown_vars then unknown_vars
                  else
                    S.union
                      unknown_vars
                      (extract_argument_vars senv env) (* 引数変数を関係しているものとして加える *)
       in
       UpBound {localEnv = local_env'
               ;vars = vars
               ;require = require})
(* ここで、env2formulaして、fvをとる、下のqformula_of_boundでも同じようにやる
        しかし、envを持つ理由が汚い気がする*)
   
   
   

let qformula_of_bound senv assign = function
  |UpBound {localEnv = env; vars = vars; require = (delta, phi) } ->  (* env|- p -> \phi *)
    let env_phi = Liq.env_substitute_F assign env
                  |> Liq.env2formula_all
                  |> Formula.list_and
                  |> List.filter (function |Formula.Unknown _ -> false
                                           | _ -> true
                                 )
    in
    let delta_phi = Liq.env2formula_all delta (* delat contain no unknown p *)
                    |> Formula.list_and
    in
    let qformula_premise = delta_phi@env_phi in
    let qformula_fv =
      List.fold_left
        (fun acc phi ->
          (Formula.fv_sort_include_v phi)@acc)
        []
        (phi::qformula_premise)
      |> List.uniq      
    in
    let binding =
      List.filter (fun (x,sch) -> not (Formula.Senv.mem x senv)) qformula_fv
    in
    Formula.QAll (binding, qformula_premise, phi)

  |LowBound {localEnv = env; vars = vars; require = phi } ->  (* env|- p -> \phi *)
    let env_phi = Liq.env_substitute_F assign env
                  |> Liq.env2formula_all
                  |> Formula.list_and
                  |> List.filter (function |Formula.Unknown _ -> false
                                           | _ -> true
                                 )
    in
    let qformula_fv =
      List.fold_left
        (fun acc phi ->
          (Formula.fv_sort_include_v phi)@acc)
        []      
        (phi::env_phi)
    |> List.uniq
    in
    let binding =
      List.filter (fun (x,sch) -> not (Formula.Senv.mem x senv)) qformula_fv
    in
    Formula.QExist (binding, phi::env_phi)

    
    
type t = |UnBound of {waitNum: int ref
                     ;senv:Formula.Senv.t
                     ;pendingSubst: Formula.subst
                     ;pendingSortSubst: Formula.sort_subst
                     ;position: pPosition
                     }
         |Bound of {waitNum: int ref (* waitNum >= 1 *)
                   ;firstWaitNum: int
                   ;senv:Formula.Senv.t
                   ;pendingSortSubst: Formula.sort_subst
                   ;bound: bound}
         |Fixable of {senv:Formula.Senv.t
                     ;pendingSortSubst: Formula.sort_subst
                     ;pol: Polarity.t (* pol fixable or neg fixable *)
                     ;bound: bound}


let of_string = function
  |UnBound rc ->
    let sita_str = List.map
                     (fun (s, p) -> Printf.sprintf "%s->%s" s (Formula.p2string p))
                     (M.bindings rc.pendingSubst)
                   |> String.concat ";"
    in
    "UnBound[sita:"^sita_str^"]"
  |Bound rc -> "Bound["^(string_of_bound rc.bound)
  |Fixable rc -> "Fixable["^(string_of_bound rc.bound)


let count_othere_p t graph assign =
  match t with
  |Bound rc ->
    S.fold
      (fun p acc ->
        PMap.add (G.pLavel_of_id graph p) 1 acc) (* とりあえずここは今の所不正確 *)
      (unknown_in_localEnv assign rc.bound)
      PMap.empty
  |Fixable rc ->
    S.fold
      (fun p acc ->
        PMap.add (G.pLavel_of_id graph p) 1 acc) (* とりあえずここは今の所不正確 *)
      (unknown_in_localEnv assign rc.bound)
      PMap.empty    
  | _ -> invalid_arg "count_othere_p: not bounded"
       
       
let upgrade_unbound assign p_env = function
  |UnBound {waitNum = n
           ;senv = senv
           ;pendingSubst = sita
           ;pendingSortSubst = sort_sita
           ;position = position } when !n = 0 ->
    let bound = mk_bound assign senv p_env sita position in
    let wait_ps = wait_predicates assign senv bound in
    let wait_num = S.cardinal wait_ps in
    if wait_num = 0 then
      let pol = predicate_polarity_of_bound bound in
      let fixable = Fixable {senv = senv
                            ;pendingSortSubst = sort_sita
                            ;pol = pol
                            ;bound = bound}
      in
      (fixable, S.empty)      
    else
      (Bound {waitNum = ref wait_num
             ;firstWaitNum = wait_num
             ;senv = senv
             ;pendingSortSubst = sort_sita
             ;bound = bound}
      , wait_ps)
    
    
  |UnBound _ -> invalid_arg "unbound_to_bound: not yet bounded"
  |Bound _ |Fixable _ -> invalid_arg "unbound_to_bound: already bounded"
                       
                       
                       
let try_to_fix assign = function
  |Fixable rc ->
    let qformula = qformula_of_bound rc.senv assign rc.bound in
    (* ここで、sort_sitaを逆に適用する必要がある*)    
    let qformula =
      M.fold
        (fun a sort acc->
          Formula.sort_swap2qformula sort (AnyS a) acc)
        rc.pendingSortSubst
      qformula
    in          
      Some qformula
  |_ ->
    None

(* unboudのwaitnumをdecrementする。0になったらwait predicateを再計算し、新たなboundをreturnする *)
let decr_wait_num assign graph p c ~change:fixability =
  match fixability with
  |Fixable _ -> invalid_arg "Fixability.decr_wait_num: can not decrement"
  |Bound rc ->
    let wait_num = rc.waitNum in
    let () = decr wait_num in
    if !wait_num = 0 then
      let new_wait_pc = wait_predicates assign rc.senv rc.bound
                        |> PSet.of_id_Set graph
      in
      let new_wait_num = PSet.cardinal new_wait_pc in
      if new_wait_num = 0 then
        let pol = predicate_polarity_of_bound rc.bound in
        let fixable = Fixable {senv = rc.senv
                              ;pendingSortSubst = rc.pendingSortSubst
                              ;pol = pol
                              ;bound = rc.bound}
        in
        Some (fixable, PSet.empty)
      else
        Some (Bound {waitNum = ref new_wait_num
                    ;firstWaitNum = new_wait_num
                    ;senv = rc.senv
                    ;pendingSortSubst = rc.pendingSortSubst
                    ;bound = rc.bound}
             ,new_wait_pc)
      
    else
      None
  |UnBound rc as unbound->
    let wait_num = rc.waitNum in
    let () = decr wait_num in
    if !wait_num = 0 then
      let new_bound, wait_pc  =
        upgrade_unbound assign (G.get_p_env graph p) unbound
      in
      Some (new_bound, (PSet.of_id_Set graph wait_pc))
    else
      None

let is_fixable = function
  |Fixable _ -> true
  | _ -> false
       

module Constructor = struct

  let mk_negative_unbound ~back_env ~front_env ~pos_formula ~unknown_set (senv, sort_sita, sita, p) =
    (assert (Liq.env_empty <> back_env));
    let position = Negative {backEnv = back_env
                            ;frontEnv = front_env
                            ;posFormula = pos_formula}
    in
    UnBound {waitNum = ref (S.cardinal unknown_set)
                            ;senv = senv
                            ;pendingSubst = sita
                            ;pendingSortSubst = sort_sita
                            ;position = position}
            
  let gen_fixability_neg_from_formula graph ~back_env ~rev_front_env ~pos_formula ~unknown_set phi =
    if not (S.is_empty unknown_set) then (* unbounded *)    
      List.fold_left
        (fun acc_map -> function
          |Formula.Unknown (senv, sort_sita, sita, p) ->
            let front_env = Liq.env_rev rev_front_env in
            let unbound =
              mk_negative_unbound
                back_env front_env pos_formula unknown_set (senv, sort_sita, sita, p)
            in
            M.add p (unbound, unknown_set) acc_map
          | _ -> acc_map
        )
        M.empty
        (Formula.list_and phi)
    else                  (* bounded *)
      List.fold_left
        (fun acc_map -> function
          |Formula.Unknown (senv, sort_sita, sita, p) ->
            let front_env = Liq.env_rev rev_front_env in            
            let unbound =
              mk_negative_unbound
                back_env front_env pos_formula unknown_set (senv, sort_sita, sita, p)
            in          
            let env  = G.pLavel_of_id graph p |> G.get_p_env graph in
            let bound, wait_pc = upgrade_unbound M.empty env unbound in
            M.add p (bound, wait_pc) acc_map
          |_ -> acc_map)
        M.empty
        (Formula.list_and phi)
    
          
    
    
  
  let gen_fixability_map_neg graph env ~pos_formula ~unknown_set =
    let neg_map, _, _ = 
      Liq.env_fold_trace
        (fun back_env (x, sch) (acc_map, rev_front_env, unknown_set) ->
          match sch with
          |([], [], Liq.TScalar (_, phi)) ->
            (match Liq.schema2sort sch with
             |Some x_sort ->
               let x_var = Formula.Var (x_sort, x) in
               let phi' = (Formula.substitution (M.singleton Id.valueVar_id x_var) phi) in (* [x/_v]phi *)
               let map = gen_fixability_neg_from_formula
                           graph back_env rev_front_env pos_formula unknown_set phi'
               in
               let acc_map' = M.union (fun p m1 m2 -> Some m1) acc_map map in
               let rev_front_env' = Liq.env_add_schema rev_front_env (x, sch) in
               let unknown_set' = S.union unknown_set (Formula.extract_unknown_p phi) in
               (acc_map', rev_front_env', unknown_set')
             |None -> invalid_arg "gen_fixability_neg_from_formula"
            )
          | _ -> (acc_map, rev_front_env, unknown_set)
        )
        (fun back_env phi (acc_map, rev_front_env, unknown_set) ->
          let map = gen_fixability_neg_from_formula
                      graph back_env rev_front_env pos_formula unknown_set phi
          in
          let acc_map' = M.union (fun p m1 m2 -> Some m1) acc_map  map in
          let rev_front_env' = Liq.env_add_F rev_front_env phi in
          let unknown_set' = S.union unknown_set (Formula.extract_unknown_p phi) in
          (acc_map', rev_front_env', unknown_set')
        )
        env
        (M.empty, Liq.env_empty, unknown_set)
    in
    neg_map
          (* ここでaddするときには、accにもともとあるか確かめ、あれば先の方を優先するようにする *)

    
  let gen_fixability_map graph c =
    match c with
    |Constraint.SSub {body = (env, e1, (Formula.Unknown(senv, sort_sita, sita, p) as e2))} ->

      let env_e1 = Liq.env_add_F env e1 in      
      let neg_map = gen_fixability_map_neg graph env_e1
                               ~pos_formula:e2
                               ~unknown_set: (S.singleton p)
      in
      (* make positive fixability *)
      let unknown_set = Formula.extract_unknown_p e1 in      
      let position = Positive {env = env; negFormula = e1 } in
      let unbound = UnBound {waitNum = ref (S.cardinal unknown_set)
                            ;senv = senv
                            ;pendingSubst = sita
                            ;pendingSortSubst = sort_sita
                            ;position = position }
      in      
      if not (S.is_empty unknown_set) then 
        M.add p (unbound, unknown_set) neg_map
      else
        let env = G.pLavel_of_id graph p |> G.get_p_env graph in
        let bound, wait_pc = upgrade_unbound M.empty env unbound in
        M.add p (bound, wait_pc) neg_map
    |Constraint.SSub {body = (env, e1, e2)} ->
      (assert (S.is_empty (Formula.extract_unknown_p e2)) );
      let env_e1 = Liq.env_add_F env e1 in            
      gen_fixability_map_neg graph env_e1
                             ~pos_formula:e2
                             ~unknown_set:S.empty
    |Constraint.SWF _ -> M.empty
      
end
