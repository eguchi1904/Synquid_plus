open Extensions
open Constraint
module Liq = Type

exception InValid of Constraint.simple_cons
exception UnSat of Constraint.simple_cons

(* represent positive occurence, negative occurence of predicate in constraint *)
type polarity =  Pos | Neg

                     
(* constraintとunknown predicate　からなるグラフ構造 *)
module G:
sig
  
  type cLavel = private int
                      
  val int_of_cLavel: cLavel -> int
    
  type pLavel = private int

  val int_of_pLavel: pLavel -> int

  type cNode = {lavel:int
               ;value:Constraint.simple_cons
               ;pos:pLavel
               ;neg:pLavel list}

  type pNode = {lavel:int
               ;value:Id.t
               ;pos: cLavel list
               ;neg: pLavel list
               }

  type t = {cTable: cNode array; pTable: pNode array }

  val pos_p: t -> cLavel -> pLavel

  val neg_ps: t -> cLavel ->pLavel list
    
         
end = struct
         
  type cLavel = int

  let int_of_cLavel x = x
              
  type pLavel = int

  let int_of_pLavel x = x
              

  type cNode = {lavel:int
               ;value:Constraint.simple_cons
               ;pos:pLavel
               ;neg:pLavel list}

  type pNode = {lavel:int
               ;value:Id.t
               ;pos: cLavel list
               ;neg: pLavel list
               }

  type t = {cTable: cNode array; pTable: pNode array }
         
  let pos_p graph c_lav =
    graph.cTable.(c_lav).pos

  let neg_ps graph c_lav =
    graph.cTable.(c_lav).neg

end

    
(* Fix information (dynamic) *)
module FixState = struct

  module FixRatio = struct
    
    type t = {fixed: int ref ; must_fix: int ref }
           
  end

  type cInfo = {is_fix: bool ref
               ;unknown_p_count:  int ref
               ;unknown_up_p_count: int ref
               }
                 
  type pInfo = {is_fix: bool ref
               ;pos_ratio: FixRatio.t
               ;neg_ratio: FixRatio.t
               }


  (* 各predicate の依存関係を保持する
     例
     Cをpでfixさせるには、qがfixしてる必要がある場合
     affect: q -> [(c,p)] 
     wait:(c,p) -> 1 
   *)
             
  module Dependency = struct
    
    type pc_tuple = (G.pLavel * G.cLavel)
                  
    type t = {wait: (pc_tuple, int) Hashtbl.t
             ;affect: (pc_tuple list) array
             }

           
  end

  type t = {cTable: cInfo array; pTable: pInfo array; dependency: Dependency.t }

end

                
(* predicateの優先順位（解く順番）を管理 *)
module PriorityManager:
sig

  exception Empty
          
  type t
     
  val pop: t -> (G.pLavel * polarity )

  (* val update: t -> G.pLavel -> FixState.pInfo -> unit *)

end= struct
  
  exception Empty
          
  type priority = |AllFix | PartialFix | ZeroFix
                  
  type table = (priority * polarity) array

  module InternalQueue = struct

    type t= {allFix: G.pLavel Queue.t
            ;partilaFix: G.pLavel Queue.t
            ;zeroFix: G.pLavel Queue.t
            }


          
    let pop {allFix = top_queue
            ;partilaFix = middle_queue
            ;zeroFix = bottom_queue }
      =
      if not (Queue.is_empty top_queue) then
        (Queue.pop top_queue, AllFix)
      else if not (Queue.is_empty middle_queue) then
        (Queue.pop middle_queue, PartialFix)
      else if not (Queue.is_empty bottom_queue) then
        (Queue.pop bottom_queue, ZeroFix)
      else
        raise  Empty
      
  end
    
  type t = {table: (priority * polarity) array
           ;internalQueue: InternalQueue.t }


  let rec pop ({table = table; internalQueue = internal_queue} as queue) =
    let p, priority = InternalQueue.pop internal_queue in
    let priority', pol =  table.(G.int_of_pLavel p) in
    if priority = priority' then
      p, pol
    else                        (* updated element *)
      pop queue
    
end
                    
