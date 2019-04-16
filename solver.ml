open Extensions
open Constraint


(* 雑に分割したので、moduleのopenが汚い *)
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

  type t = {fixabilityManager: FixabilityManager.t
           ;cFixState: CFixState.t
           ;pFixableCounter: PFixableConstraintCounter.t
           ;pFixState: PFixState.t
           ;queue: PriorityQueue.t
           }

  val of_string: G.t -> t -> string

  val log: G.t -> string -> t -> unit

  val create: S.t -> G.t -> t
         (* val fix_constraint: t -> G.t -> G.pLavel -> G.cLavel -> unit *)

  val next: t -> G.t -> Formula.t M.t ->
            (G.pLavel * Polarity.t * (G.cLavel * Formula.qformula) list) option
    
  val add_fix_c: t -> G.t ->
                 'a M.t -> G.pLavel -> G.cLavel -> unit
end =  struct

  type t = {fixabilityManager: FixabilityManager.t
           ;cFixState: CFixState.t
           ;pFixableCounter: PFixableConstraintCounter.t
           ;pFixState: PFixState.t
           ;queue: PriorityQueue.t
           }

  let of_string graph t =
    let fix_manager_str = FixabilityManager.of_string graph t.fixabilityManager in
    let pfixable_counter_str = PFixableConstraintCounter.of_string graph t.pFixableCounter in
    let queue_str = PriorityQueue.to_string graph t.queue in
    "\nFixabiliy Manager\n"
    ^"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    ^ fix_manager_str
    ^"\n predicate fixable counter"
    ^"\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    ^ pfixable_counter_str
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
  let create up_ps graph =
    let up_plav_set = PSet.of_id_Set graph up_ps in
    let fixability_manager, fixable_count, pfix_state, queue = 
      FixabilityManager.Constructor.f up_plav_set graph
    in
    let cfix_state = CFixState.create up_ps graph in
    {fixabilityManager = fixability_manager
           ;cFixState = cfix_state
           ;pFixableCounter = fixable_count
           ;pFixState = pfix_state
           ;queue = queue
           }    
    


  let next t graph assign =
    match PriorityQueue.pop t.queue with
    |None -> None
    |Some (p, pol, priority) ->
      
      let sol = FixabilityManager.fix t.fixabilityManager
                                      graph assign p priority
                                      ~may_change:(t.cFixState,
                                                   t.pFixableCounter,
                                                   t.pFixState,
                                                   t.queue)
      in
      (* Fixabilityに夜、fixstateの変化を反映した後に、fixをする *)
      let () = PFixState.fix t.pFixState p
                             ~may_change:t.queue
      in
      let () = CFixState.prop_p_fix t.cFixState graph p
      in
      Some (p, pol, sol)

      
  let add_fix_c t graph assign p c =
    let () = CFixState.fix t.cFixState c in
    FixabilityManager.tell_related_predicate_constraint_is_fixed
      t.fixabilityManager graph assign t.cFixState p c
      ~may_change:(t.pFixableCounter,
                   t.pFixState,
                   t.queue
                  )

    
      
end

type validityLevel =
  |Valid
  |UnValid
  |Sat
  |UnSat
  |YetJudge
  
let check_validity graph assign state p c_lavel   =
  let cfix_state = state.DyState.cFixState in
  if CFixState.is_zero_unknown cfix_state c_lavel then
    begin
      let is_valid = G.cons_of_cLavel graph c_lavel
               |> Constraint.subst_simple_cons assign 
               |>Constraint.is_valid_simple_cons_all
      in
      if is_valid then
        DyState.add_fix_c state graph assign p c_lavel
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
        ()
      else
        invalid_arg "not implimented yet" (* refineする *)
    end
  else
    ()
    
    
    
     
let check_validity_around_p graph assign p ~may_change:state =
  let () = List.iter
             (check_validity graph assign state p)
             (G.pos_cs graph p)
  in
  let () = List.iter
             (check_validity graph assign state p)
             (G.neg_cs graph p)
  in
  ()


(* qeせずとも成立しているものは除く *)
let get_qfree_sol graph assign p_lav sol pol =
  let p = G.id_of_pLavel graph p_lav in
  let qfree_list =
    if pol = Polarity.neg then
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
    else
      List.fold_left
        (fun acc (c_lav, q_phi) -> (Qe.f q_phi)::acc)
        []
        sol
  in
  Formula.and_list qfree_list
        
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
  

let rec iter_fix graph state (qualify:QualifierAssign.t) assign = (* stateは外に置きたいほんとは *)
  match DyState.next state graph assign with
  |Some (p, pol, sol) ->
    let () = DyState.log graph ("pop:"^(G.id_of_pLavel graph p)) state in
    let fixed_cs = List.map fst sol
                 |> List.map (G.cons_of_cLavel graph)
    in
    let () = log_poped graph assign fixed_cs (p, pol, sol) in    
    let qualify_phi =
      if pol = Polarity.pos then
        QualifierAssign.get qualify graph assign p fixed_cs
      else
        QualifierAssign.get qualify graph assign p []
    in
    let qe_sol = get_qfree_sol graph assign p sol pol (* List.map Qe.f (List.map snd sol) *)
                 (* |> Formula.and_list *)
    in
    let p_assign = Formula.And (qualify_phi, qe_sol) in
    let assign' = M.add (G.id_of_pLavel graph p) p_assign assign in
    (* ここでvalidity等を検査すべき *)
    let () = check_validity_around_p graph assign' p ~may_change:state  in
    (* logging *)
    let () = log_assign "" assign' in
    iter_fix graph state qualify assign'
  |None -> assign
    
    

      
    
        
let f up_ps qualifyers cs =
  let graph = G.create up_ps cs in
  let () = G.log graph in
  let state = DyState.create up_ps graph in
  let qualify_assign = M.empty in (* とりあえず *)
  let qualify = QualifierAssign.create graph qualify_assign in
  let assign = iter_fix graph state qualify M.empty in
  let sita_debug = M.bindings assign in
  assign


      
