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

module PredicateFixableLevel:
sig
  type t = private (int * int)
  val fixed: t
  val all: int -> t
  val partial: t
  val zero: t
end

module Priority:
sig
  type t = {fixLevel: PredicateFixableLevel.t
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
  
 type fixRatio = {fixable: int ref ; unfixable: int ref }

  type pInfo = {isFix: bool ref
               ;isUpp: bool 
               ;posRatio: fixRatio
               ;negRatio: fixRatio
               }

  type t 

  val calc_priority: t -> G.pLavel -> Priority.t

  val fix: t -> G.pLavel -> unit

end

     
module CFixState:
sig
  type t

  val is_fixed: t -> G.cLavel -> bool

end

module FixablilityManager:
sig
  type t
     
end
     
         

(* val f :    hints: Formula.t list M.t *)
(*         -> objective_predicates: Id.t list  *)
(*         -> constraints: Constraint.simple_cons list *)
(*         -> Formula.t M.t *)
        
