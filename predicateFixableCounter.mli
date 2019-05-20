module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
module Polarity = PredicatePriorityQueue.Polarity
module PFixState = PredicateFixState
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
                     
type fixRatio = {fixable: int ref ; unfixable: int ref }


type t  =private {posRatio: fixRatio array
                 ;negRatio: fixRatio array
                 ;outerRatio: fixRatio option array                 
                 }
               
val of_string:G.t -> t -> string
   
(* val decr_pos_unfix: t -> G.pLavel -> unit *)
   
(* val decr_neg_unfix: t -> G.pLavel -> unit *)
   
val unfixable2fixable: t -> G.t -> G.pLavel -> G.cLavel -> Polarity.t
                       -> (unit -> int PMap.t) 
                       -> (unit -> int PMap.t) option
                       -> may_change:(PFixState.t * PriorityQueue.t)
                       -> unit
  
val remove_fixable: t -> G.t -> G.pLavel -> G.cLavel -> Polarity.t
                       -> (unit -> int PMap.t) 
                       -> may_change:(PFixState.t * PriorityQueue.t)
                       -> unit

  
val remove_unfixable: t -> G.t -> G.pLavel -> G.cLavel -> Polarity.t
                       -> (unit -> int PMap.t) 
                       -> (unit -> int PMap.t) option
                       -> may_change:(PFixState.t * PriorityQueue.t)
                       -> unit

module Constructor:
sig
  val dummy_ratio : fixRatio
  val create : int -> t

  val outer_registor :
    t -> G.pLavel -> (int * int * (unit -> int PMap.t)) option
    -> change:PredicateFixState.t -> unit
    
  val pos_registor :
    t -> G.t 
    -> G.pLavel 
    -> int -> int 
    -> (unit -> int PMap.t) 
    -> (unit -> int PMap.t) option 
    -> change:PredicateFixState.t * PriorityQueue.t
    -> unit
    
  val neg_registor :
    t -> G.t 
    -> G.pLavel 
    -> int -> int 
    -> (unit -> int PMap.t) 
    -> (unit -> int PMap.t) option 
    -> change:PredicateFixState.t * PriorityQueue.t
    -> unit

end

    
