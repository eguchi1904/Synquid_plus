open Extensions
open Constraint


(* 雑に分割したので、moduleのopenが汚いな *)
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

  type t
     
         (* val fix_constraint: t -> G.t -> G.pLavel -> G.cLavel -> unit *)

  val next: t -> G.t -> Formula.t M.t ->
            (G.pLavel * Polarity.t * (G.cLavel * Formula.qformula) list) option

end =  struct

  type t = {fixabilityManager: FixabilityManager.t
           ;cFixState: CFixState.t
           ;pFixableCounter: PFixableConstraintCounter.t
           ;pFixState: PFixState.t
           ;queue: PriorityQueue.t
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
      Some (p, pol, sol)
      
end

    


let rec iter_fix graph state qualify assign = (* stateは外に置きたいほんとは *)
  match DyState.next state graph assign with
  |Some (p, pol, sol) ->
    let fixed_cs = List.map fst sol
                 |> List.map (G.cons_of_cLavel graph)
    in
    let qualify_phi =
      if pol = Polarity.pos then
        QualifierAssign.get qualify graph assign p fixed_cs
      else
        QualifierAssign.get qualify graph assign p []
    in
    let qe_sol = List.map Qe.f (List.map snd sol)
                 |> Formula.and_list
    in
    let p_assign = Formula.And (qualify_phi, qe_sol) in
    let assign' = M.add (G.id_of_pLavel graph p) p_assign assign in
    (* ここでvalidity等を検査すべき *)
    iter_fix graph state qualify assign'
  |None -> assign
    
    

      
    
        
    


      
