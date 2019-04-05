exception InValid of Constraint.simple_cons
exception UnSat of Constraint.simple_cons

module Polarity:
sig
  type t = private int
  val pos: t
  val neg: t
end

module G:
sig
  
  type cLavel = private int
                      
  val int_of_cLavel: cLavel -> int
    
  type pLavel = private int

  val int_of_pLavel: pLavel -> int


  type t

  val pos_p: t -> cLavel -> pLavel

  val neg_ps: t -> cLavel ->pLavel list
    
end

module PMap: sig type 'a t end
     
module PG:
sig

  type t

  val pos_ps: t -> G.pLavel -> G.pLavel list

  val neg_ps: t -> G.pLavel -> G.pLavel list    

end
     
  
module PredicateFixableLevel:
sig
  type t = int 
  val all: t
  val partial: t
  val zero: t
end

module Priority:
sig
  type t = {fixLevel: PredicateFixableLevel.t
           ;othereUnknown: int
           ;fixableNum:int
           ;pol: Polarity.t
           ;lavel: G.pLavel }     
end


module PriorityQueue:
sig

  type t

  val pop: t -> (G.pLavel * Priority.t) option

  val push: t -> G.pLavel -> Priority.t -> unit

  val update: t -> G.pLavel -> Priority.t -> unit
    
end


     
module PFixState:
sig
  
  type state = |Fixed of state
               |AllFixable of (int * int PMap.t)
               |PartialFixable
               |ZeroFixable


  type t
     
  (* 呼び出し時点で、pをfixしたことによる、fixableLevelの変化は反映されていないといけない *)
  val fix: t -> G.pLavel -> unit
    
  (* 呼び出し時点で、pをunfixしたことによる、fixableLevelの変化は反映されていないといけない *)
  val unfix: t -> G.pLavel -> unit

  val pos_update2allfixable: t -> G.pLavel -> int PMap.t -> unit

  val neg_update2allfixable: t -> G.pLavel -> int PMap.t -> unit    
  (* 上がるのにも下がるのにも対応する *)
  val pos_update: t ->  G.pLavel -> PredicateFixableLevel.t -> unit

  val neg_update: t ->  G.pLavel -> PredicateFixableLevel.t -> unit    

  val calc_priority : t -> G.pLavel -> bool -> Priority.t

end
     
(* hint *)

     
module PFixableConstraintCounter:
sig
  
 type fixRatio = {fixable: int ref ; unfixable: int ref }

  type pInfo = {isFix: bool ref
               ;isUpp: bool 
               ;posRatio: fixRatio
               ;negRatio: fixRatio
               }

  type t 

  val calc_priority: t -> G.pLavel -> Priority.t



end


module CFixState:
sig
  type t

  val is_fixed: t -> G.cLavel -> bool

end     
     

module FixablilityManager:
sig
  type t

  val fix: t -> G.t -> Formula.subst -> G.pLavel -> Priority.t 
           -> may_change:(CFixState.t * PFixState.t * PFixableConstraintCounter.t * PriorityQueue.t) 
           -> Formula.t list * G.cLavel list
end
     
         

(* val f :    hints: Formula.t list M.t *)
(*         -> objective_predicates: Id.t list  *)
(*         -> constraints: Constraint.simple_cons list *)
(*         -> Formula.t M.t *)
        
