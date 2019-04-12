module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
module Polarity = PredicatePriorityQueue.Polarity
module PFixState = PredicateFixState
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
                     
type fixRatio = {fixable: int ref ; unfixable: int ref }


  type t 

         (* val decr_pos_unfix: t -> G.pLavel -> unit *)

         (* val decr_neg_unfix: t -> G.pLavel -> unit *)
     
  val unfixable2fixable: t -> G.pLavel -> Polarity.t -> (unit -> int PMap.t) ->
                         may_change:(PFixState.t * PriorityQueue.t) -> unit

  val remove_fixable: t -> G.pLavel -> Polarity.t -> (unit -> int PMap.t) ->
                      may_change:PFixState.t * PriorityQueue.t -> unit

  val remove_unfixable: t -> G.pLavel -> Polarity.t -> (unit -> int PMap.t) ->
                         may_change:PFixState.t * PriorityQueue.t -> unit
