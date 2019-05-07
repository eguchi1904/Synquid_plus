open Extensions
open Constraint


(* 雑に分割したので、moduleのopenが汚い *)
module Liq = Type
module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
module CSet = ConsGraph.CSet
            
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority

module PFixState = PredicateFixState

module PFixableConstraintCounter = PredicateFixableCounter

module CFixState = ConstraintFixState
                 

exception InValid of Constraint.simple_cons
exception UnSat of Constraint.simple_cons
exception RefineErr of string


(* unknown p が入っていて良い、無視する *)
let refine assign c=
  let open Constraint in
  match c with
  |SSub (_, _, Formula.Unknown(_, sort_sita, sita, p)) ->
    let c' = Constraint.subst_simple_cons assign c
             |> Constraint.replace_unknown_p_to_top
    in
    (match c' with
     |SSub (env, e, _) ->
       let p_phi_list = M.find p assign |> Formula.list_and in
       let env_phi = Liq.env2formula_all env in
       let p_phi_list =
       List.filter
         (fun phi ->
           let phi' = Formula.substitution sita phi
                      |> Formula.sort_subst2formula sort_sita
           in
           let psi =
             (Formula.Implies ((Formula.And(env_phi,e), phi')))
           in
           let z3_psi,_ = UseZ3.convert psi in
           UseZ3.is_valid z3_psi
         )
         p_phi_list
       in
       (p, Formula.and_list p_phi_list)
     |_ -> assert false
    )
  |_ -> raise (RefineErr "cant refine")
              
    
let log_och = open_out "solver.log"

let log_assign mes assign =
  let assign_list = M.bindings assign in
  let assign_str =
    List.map (fun (k_i, e) ->
        Printf.sprintf "  %s -> [ %s ]" k_i (Formula.p2string e))
             assign_list
    |> String.concat "\n"
  in
  Printf.fprintf
    log_och
    "%s:\n\n%s\n\n\n\n\n\n\n\n"
    mes
    assign_str

let log_poped graph assign fixed_cs (p, pol, sol) =
  let fixed_cs = List.map (Constraint.subst_simple_cons assign) fixed_cs in
  let fixed_cs_str = Constraint.scons_list_to_string fixed_cs in
  let sol_str =
    List.map (fun (c, qf) -> Printf.sprintf "%d:\n%s"
                                            (G.int_of_cLavel c)
                                            (Formula.qformula2string qf)
             )
             sol
    |> String.concat "------------------------------\n"
  in
  Printf.fprintf
    log_och
    "\n\n\n\npoped p:%d (%s)\n --- polarity = %s\nfixing constraints\n%s\nqformula is\n %s "
    (G.int_of_pLavel p)
    (G.id_of_pLavel graph p)
    (Polarity.of_string pol)
    fixed_cs_str
    sol_str
  
     
   
module QualifierAssign = struct

  type t = Formula.t array

  let create graph qualifier_assign =
    let p_num = G.pNode_num graph in
    let t = Array.make p_num (Formula.Bool true) in
    let () = G.iter_p
               (fun p_lav ->
                 let p = G.id_of_pLavel graph p_lav in
                 match M.find_opt p qualifier_assign with
                 |Some p_quali ->
                   t.(G.int_of_pLavel p_lav) <- p_quali
                 |None -> ())
               graph
    in
    t
    

  let refine_qualifiers assign p cs = (* p \in assign *)
    List.fold_left
      (fun acc_assign c ->
        let p', p_phi' = refine acc_assign c in
        if p <> p' then invalid_arg "refine_qualifiers: "
        else
          M.add p p_phi' acc_assign)
    assign
    cs
        
        
         
  let get t graph assign p cs =       (* csを満たすようなqualifierを返す *)
    let p_quali = t.(G.int_of_pLavel p) in
    let p_id = G.id_of_pLavel graph p in
    let assign' = M.add p_id p_quali assign in
    let assign'' = refine_qualifiers assign' p_id cs in
    let p_quali' = M.find p_id assign'' in
    (t.(G.int_of_pLavel p) <- p_quali'); (* これは要実験 *)
    p_quali'
    
end


                
module DyState:
sig

  type t = {qualifierAssign: QualifierAssign.t
           ;fixabilityManager: FixabilityManager.t
           ;cFixState: CFixState.t
           ;pFixableCounter: PFixableConstraintCounter.t
           ;pFixState: PFixState.t
           ;queue: PriorityQueue.t
           }

  val of_string: G.t -> t -> string

  val log: G.t -> string -> t -> unit

  val create: S.t -> G.t -> Formula.t M.t ->  t
         (* val fix_constraint: t -> G.t -> G.pLavel -> G.cLavel -> unit *)

  val next: t -> G.t -> Formula.t M.t ->
            (Formula.t M.t) option

end =  struct

  type t = {qualifierAssign: QualifierAssign.t
           ;fixabilityManager: FixabilityManager.t
           ;cFixState: CFixState.t
           ;pFixableCounter: PFixableConstraintCounter.t
           ;pFixState: PFixState.t
           ;queue: PriorityQueue.t
           }

  let of_string graph t =
    let fix_manager_str = FixabilityManager.of_string graph t.fixabilityManager in
    let pfixable_counter_str = PFixableConstraintCounter.of_string graph t.pFixableCounter in
    let pfix_state_str = PFixState.to_string graph t.pFixState in
    let queue_str = PriorityQueue.to_string graph t.queue in
    "\nFixabiliy Manager\n"
    ^"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    ^ fix_manager_str
    ^"\n predicate fixable counter"
    ^"\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    ^ pfixable_counter_str
    ^"\n predicate fix state"
    ^"\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    ^ pfix_state_str    
    ^"\n queue\n"
    ^"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    ^ queue_str

  let log_dystate_och = open_out "dyState.log"
                      
  let log graph mes t =
    Printf.fprintf
      log_dystate_och
      "%s\n--------------------------------------------------%s\n--------------------------------------------------\n\n\n\n"
      mes
      (of_string graph t)
  
  (* 初期状態を作成する *)
  let create up_ps graph qualifier_assign =
    let up_plav_set = PSet.of_id_Set graph up_ps in
    let fixability_manager, fixable_count, pfix_state, queue = 
      FixabilityManager.Constructor.f up_plav_set graph
    in
    let cfix_state = CFixState.create up_ps graph in
    {qualifierAssign = QualifierAssign.create graph qualifier_assign
    ;fixabilityManager = fixability_manager
    ;cFixState = cfix_state
    ;pFixableCounter = fixable_count
    ;pFixState = pfix_state
    ;queue = queue
    }

let get_qfree_sol graph assign p_lav sol pol fixability =
  let p = G.id_of_pLavel graph p_lav in
  if pol = Polarity.neg then
    (* qeせずとも成立しているものは除く *)
    let qfree_list =    
      List.fold_left
        (fun acc (c_lav, q_phi) ->
          let c = G.cons_of_cLavel graph c_lav in
          let assign' = M.add p (Formula.Bool true) assign in
          let already_valid = Constraint.subst_simple_cons assign' c
                              |>Constraint.replace_unknown_p_to_top
                              |>Constraint.is_valid_simple_cons
          in
          if already_valid then acc
          else (Qe.f q_phi)::acc)
        []
        sol
    in
    Formula.and_list qfree_list
  else
    let qfree_list =
      List.fold_left
        (fun acc (c_lav, q_phi) ->
          let qe_phi = (Qe.f q_phi)
                       (* ひとまず、pass conditionのような、_vを含まないようなものを排除する *)
                       |> Formula.list_and
                       |> List.filter (fun phi ->
                              S.mem Id.valueVar_id (Formula.fv_include_v phi))
                       |> Formula.and_list
          in
            qe_phi::acc
        )
        []
        sol
    in
    if qfree_list = [] then Formula.Bool false
    else
      let c_list = List.map fst sol
                   |> List.map (G.cons_of_cLavel graph)
      in
      let qfree_list =
        List.filter
          (fun phi ->
            let assign' = M.add p phi assign in
            List.for_all
              (fun c ->
                Constraint.subst_simple_cons assign' c
                |> Constraint.replace_unknown_p_to_top
                |> Constraint.is_valid_simple_cons)
              c_list)
          qfree_list
      in
      Formula.and_list qfree_list
      

(* qeして、qualifyと適切に結合させて解をえる *)
  let mk_new_assign graph assign qualify p pol fixability sol =
    let fixed_cs = List.map fst sol
                 |> List.map (G.cons_of_cLavel graph)
    in    
    let qualify_phi =
      if pol = Polarity.pos then
        QualifierAssign.get qualify graph assign p fixed_cs
      else
        QualifierAssign.get qualify graph assign p []
    in
    let qe_sol = get_qfree_sol graph assign p sol pol fixability (* List.map Qe.f (List.map snd sol) *)
                 (* |> Formula.and_list *)
    in
    let p_assign =Formula.and_list [qualify_phi; qe_sol] in
    M.add (G.id_of_pLavel graph p) p_assign assign


  
    
  let check_validity graph assign p c_lavel ~may_change:cfix_state =
    if CFixState.is_zero_unknown cfix_state c_lavel then
      begin
        let is_valid = G.cons_of_cLavel graph c_lavel
                       |> Constraint.subst_simple_cons assign 
                       |>Constraint.is_valid_simple_cons_all
        in
        if is_valid then
          let () = CFixState.fix cfix_state c_lavel in
          true
        else
          invalid_arg "not implimented yet" (* refineする *)
      end
    else if CFixState.is_only_upp_p cfix_state c_lavel then
      begin
        let is_sat = G.cons_of_cLavel graph c_lavel
                     |>Constraint.subst_simple_cons assign 
                     |>Constraint.replace_unknown_p_to_top (* ここでupp pを排除する *)
                     |>Constraint.is_satisifiable_simple_cons_all
        in
        if is_sat then
          false
        else
          invalid_arg "not implimented yet" (* refineする *)
      end
    else
      false
    
    
     
  let check_validity_around_p graph assign p ~may_change:cfix_state =
    let new_valid_cs_pos =
      (G.pos_cs graph p)
      |> CSet.of_list
      |> CSet.filter (CFixState.isnt_fixed cfix_state)
      |> CSet.filter (check_validity graph assign p ~may_change:cfix_state) 
    in
    let new_valid_cs_neg =
      (G.neg_cs graph p)
      |> CSet.of_list      
      |> CSet.filter (CFixState.isnt_fixed cfix_state)
      |> CSet.filter (check_validity graph assign p ~may_change:cfix_state)     
    in
    CSet.union new_valid_cs_neg new_valid_cs_pos |> CSet.elements

    

  let next t graph assign =
    match PriorityQueue.pop t.queue with
    |None -> None
    |Some (p, pol, priority) ->

      let () =
        log graph ("pop:"^(G.id_of_pLavel graph p)
                   ^"priority:"^(Priority.to_string graph priority)) t
      in
      let () = PFixState.fix t.pFixState p
                             ~may_change:t.queue
      in
      let () = CFixState.prop_p_fix t.cFixState graph p in
      let sol, fixed_cs = FixabilityManager.pull_solution
                                t.fixabilityManager
                                graph assign p priority
                                ~may_change:t.cFixState
      in
      let fixed_cs_log =  List.map fst sol
                      |> List.map (G.cons_of_cLavel graph)
      in      
      (* logging: navely add from iter_fix *)
      let () = log_poped graph assign fixed_cs_log (p, pol, sol) in
      let fixability = priority.fixLevel in
      let assign' = mk_new_assign graph assign t.qualifierAssign
                                  p pol fixability sol in
      let additional_fix_cs = check_validity_around_p graph assign' p
                                                      ~may_change:t.cFixState
      in
      (* propagate  *)
      let () = FixabilityManager.propagate_c_fixed_info
                 t.fixabilityManager
                 graph assign' t.cFixState (additional_fix_cs@fixed_cs)
                 ~may_change:(t.pFixableCounter,
                              t.pFixState,
                              t.queue)
      in
      let () = FixabilityManager.propagate_p_fixed_info
                 t.fixabilityManager
                 graph assign' t.cFixState p 
                 ~may_change:(t.pFixableCounter,
                             t.pFixState,
                             t.queue)
      in

      let () = log_assign "" assign' in
      Some assign'
      
end

    
  

let rec iter_fix graph state assign = (* stateは外に置きたいほんとは *)
  match DyState.next state graph assign with
  |Some new_assign ->
    iter_fix graph state new_assign
  |None -> assign
    
    
        
let f up_ps neg_ps qualifyers cs =
  let graph = G.create up_ps neg_ps cs in
  let () = G.log graph in
  let qualify_assign = M.empty in (* とりあえず *)  
  let state = DyState.create up_ps graph qualify_assign in
  let assign = iter_fix graph state  M.empty in
  let sita_debug = M.bindings assign in
  assign


      
