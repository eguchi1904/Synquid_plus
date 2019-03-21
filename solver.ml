open Extensions
open Constraint

   
module Liq = Type
module Heap = Core.Heap         (* heapのためだけに、Core依存 *)

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

  type fixRatio = {fixed: int ref ; unfixed: int ref }

  type cInfo = {isFix: bool ref
               ;unknown_p_count:  int ref
               ;unknown_up_p_count: int ref
               }
                 
  type pInfo = {isFix: bool ref
               ;isUpp: bool 
               ;posRatio: fixRatio
               ;negRatio: fixRatio
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
          
  (* type t *)

  (* raise Empty if empty *)
  val pop: t -> (G.pLavel * polarity )

  (* val update: t -> G.pLavel -> (FixState.pInfo) -> unit  *)

end= struct
  
  exception Empty
          

  module FixableLevel:
  sig
    type t = private int
    val all_fixable: t
    val partial_fixable: t
    val zero_fixable: t
  end = struct
    type t =  int
    let all_fixable = 0
    let partial_fixable = 1
    let zero_fixable = 2
  end

  module PolarityPreference:
  sig
    type t = private int
    val pos: t
    val neg: t
    val of_pol: polarity -> t
  end = struct
    type t = int
    (* positive    *)
    let pos = 0
    let neg = 1
    let of_pol = function
      |Pos -> pos
      |Neg -> neg
  end
           

  (* lex-order *)
  type priority = {fixLevel: FixableLevel.t
                  ;fixableNum:int
                  ;pol: PolarityPreference.t
                  ;lavel: G.pLavel }
                  
  type table = (priority * polarity) array

  module InternalQueue = struct

    type t = priority Heap

          
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

    let add  {allFix = top_queue
             ;partilaFix = middle_queue
             ;zeroFix = bottom_queue }    p priority  =
      match priority with
      |AllFix -> Queue.add p top_queue
      |PartialFix -> Queue.add p middle_queue
      |ZeroFix -> Queue.add p bottom_queue     

  end

    
  type t = {table: (priority * polarity) array
           ;internalQueue: InternalQueue.t
           }


  let rec pop ({table = table; internalQueue = internal_queue} as queue) =
    let p, priority = InternalQueue.pop internal_queue in
    let priority', pol =  table.(G.int_of_pLavel p) in
    if priority = priority' then
      p, pol
    else                        (* updated old element *)
      pop queue


  let priority_of_fixRatio {fixed = fixed; unfixed =unfixed} p pol=
    let fixable_level = if !fixed = 0 then
                          FixableLevel.all_fixable
                        else if !fixed <> !unfixed then
                          FixableLevel.partial_fixable
                        else
                          FixableLevel.zero_fixable
    in
    {fixLevel = fixablelevel
      ;fixableNum = !fixed
      ;pol = PolarityPreference.of_pol pol
      ;lavel = p
    }
    
  let calc_priority FixState.{is_fix = _
                             ;isUpp = is_upp
                             ;posRatio = pos_ratio
                             ;negRatio = neg_ratio}
    =
    if is_upp then
      priority_of_fixRatio pos_ratio p Pos
    else
      let pos_priority = priority_of_fixRatio pos_ratio in
      let neg_priority = priority_of_fixRatio neg_ratio in
      if pos_priority < neg_priority then
        pos_priority
      else
        neg_priority

    
  let update {table = table; internalQueue = internal_queue} p (priority, pol) =
    table.(G.int_of_pLavel p) <- (priority, pol); (* table kept up to date *)
    InternalQueue.add internal_queue p priority  
    
end
                    
