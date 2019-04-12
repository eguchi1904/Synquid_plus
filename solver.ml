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


   
   
               
module DyState:
sig

  type t
     
         (* val fix_constraint: t -> G.t -> G.pLavel -> G.cLavel -> unit *)

  val next: t -> G.t -> Formula.t M.t ->
            (G.pLavel * (G.cLavel * Formula.qformula) list) option

end = struct
   
  type t = {fixabilityManager: FixabilityManager.t
           ;cFixState: CFixState.t
           ;pFixableCounter: PFixableConstraintCounter.t
           ;pFixState: PFixState.t
           ;queue: PriorityQueue.t
           }
             (* let tell_constraint_pos_predicate_is_fixed t graph p c = *)

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
      Some (p, sol)
    


         

end　
