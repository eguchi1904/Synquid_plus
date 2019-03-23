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
module FixState:
sig
  
 type fixRatio = {fixable: int ref ; unfixable: int ref }

  type cInfo = {isFix: bool ref
               ;unknown_p_count:  int ref
               ;unknown_up_p_count: int ref
               }


  (* !isFIx = trueの時、他のレコードは無意味な値 *)
  type pInfo = {isFix: bool ref
               ;isUpp: bool 
               ;posRatio: fixRatio
               ;negRatio: fixRatio
               }

  module Dependency:
  sig

    exception Cons_pred_mismatch
            
    type pc_tuple = (G.cLavel * G.pLavel)
                  
    type t = {wait: (pc_tuple, int) Hashtbl.t
             ;affect: (pc_tuple list) array
             }
  end
  
     
  type t = {cTable: cInfo array; pTable: pInfo array; dependency: Dependency.t}
         

  val set_constraint_is_fixed: t -> G.cLavel -> unit

  val is_predicate_fixed: t -> G.pLavel -> bool

  val is_constraint_fixed: t -> G.cLavel -> bool

  val get_p_info: t -> G.pLavel -> pInfo
    
  val get_pos_unfixable: t -> G.pLavel -> int ref

  val get_pos_fixable: t -> G.pLavel -> int ref

  val get_neg_unfixable: t -> G.pLavel -> int ref

  val get_neg_fixable: t -> G.pLavel -> int ref    

  val is_fixable: t -> G.cLavel -> G.pLavel -> bool (* dependecy を参照 *)
    
  (* val decr_pos_unfix: t -> G.pLavel -> unit *)

  (* val decr_neg_unfix: t -> G.pLavel -> unit *)
    
end= struct
  

  type fixRatio = {fixable: int ref ; unfixable: int ref }

  type cInfo = {isFix: bool ref
               ;unknown_p_count:  int ref
               ;unknown_up_p_count: int ref
               }


  (* !isFIx = trueの時、他のレコードは無意味な値 *)
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

    exception Cons_pred_mismatch
            
    type pc_tuple = (G.cLavel * G.pLavel)
                  
    type t = {wait: (pc_tuple, int) Hashtbl.t
             ;affect: (pc_tuple list) array
             }

    let wait_num_to_be_fixable t c p =
      try
        Hashtbl.find t.wait (c,p)
      with
        _ -> raise Cons_pred_mismatch
           
  end

  type t = {cTable: cInfo array; pTable: pInfo array; dependency: Dependency.t }

  let set_constraint_is_fixed t c =
    t.cTable.(G.int_of_cLavel c).isFix := true

  let is_constraint_fixed t c = !(t.cTable.(G.int_of_cLavel c).isFix)

  let is_predicate_fixed t p = !(t.pTable.(G.int_of_pLavel p).isFix)

  let get_p_info t p =
    t.pTable.(G.int_of_pLavel p)
    
  let get_pos_unfixable t p =
    t.pTable.(G.int_of_pLavel p).posRatio.unfixable

  let get_neg_unfixable t p =
    t.pTable.(G.int_of_pLavel p).negRatio.unfixable

  let get_pos_fixable t p =
    t.pTable.(G.int_of_pLavel p).posRatio.fixable

  let get_neg_fixable t p =
    t.pTable.(G.int_of_pLavel p).negRatio.fixable    
    
  let is_fixable t c p =
    (Dependency.wait_num_to_be_fixable t.dependency c p) = 0
    

end

                
(* predicateの優先順位（解く順番）を管理 *)
module PriorityManager:
sig
  
  type t

  (* onece (p, _) is poped, p never be poped again unless pushed *)
  val pop: t -> (G.pLavel * polarity ) option

  val push: t -> G.pLavel -> FixState.t -> unit
  (* push queue p fix_sate
     will update priority of p if p already exists in queue *)

  val update: t -> G.pLavel -> FixState.t -> unit
    
end= struct
  
  module FixableLevel:
  sig
    type t = private int
    val already_fixed: t
    val all_fixable: t
    val partial_fixable: t
    val zero_fixable: t
  end = struct
    type t =  int
    let already_fixed = -1            
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
    val to_pol: t -> polarity
  end = struct
    type t = int
    (* positive    *)
    let pos = 0
    let neg = 1
            
    let of_pol = function
      |Pos -> pos
      |Neg -> neg
            
    let to_pol n =
      if n = pos then Pos
      else if n = neg then Neg
      else assert false
      
  end
           

  (* the most important factor is fixable level. *)
  type priority = {fixLevel: FixableLevel.t
                  ;fixableNum:int
                  ;pol: PolarityPreference.t
                  ;lavel: G.pLavel }

                  
  module InternalQueue:
  sig

    type t = private priority Heap.t

    val pop: t -> (G.pLavel * priority) option

    val push: t -> G.pLavel -> priority -> unit

  end = struct

    type t = priority Heap.t

    let pop heap =
      match Heap.pop heap with
      |None -> None
      |Some priority -> Some (priority.lavel, priority)

      
    let push heap p priority= Heap.add heap priority

  end

    
  type t = {table: priority array
           ;internalQueue: InternalQueue.t
           }


  let rec pop ({table = table; internalQueue = internal_queue} as queue) =
    match InternalQueue.pop internal_queue with
    |None -> None
    |Some (p, priority) ->
      let priority' =  table.(G.int_of_pLavel p) in
      if priority = priority' then
        (* insert dummy priority into table *)
        let () = table.(G.int_of_pLavel p) <-  {fixLevel = FixableLevel.already_fixed
                                               ;fixableNum = priority.fixableNum
                                               ;pol =  priority.pol
                                               ;lavel = priority.lavel}
        in
        Some (p, PolarityPreference.to_pol priority.pol)
      else                        (* updated old element *)
        pop queue


  let priority_of_fixRatio FixState.{fixable = fixable; unfixable =unfixable} p pol=
    let fixable_level = if !fixable = 0 then
                          FixableLevel.all_fixable
                        else if !fixable <> !unfixable then
                          FixableLevel.partial_fixable
                        else
                          FixableLevel.zero_fixable
    in
    {fixLevel = fixable_level
      ;fixableNum = !fixable
      ;pol = PolarityPreference.of_pol pol
      ;lavel = p
    }

    
  let calc_priority p FixState.{isFix = _
                               ;isUpp = is_upp
                               ;posRatio = pos_ratio
                               ;negRatio = neg_ratio}
    =
    if is_upp then
      priority_of_fixRatio pos_ratio p Pos
    else
      let pos_priority = priority_of_fixRatio pos_ratio p Pos in
      let neg_priority = priority_of_fixRatio neg_ratio p Neg in
      if pos_priority < neg_priority then
        pos_priority
      else
        neg_priority

  let push {table = table; internalQueue = internal_queue} p fix_state =
    let p_info = FixState.get_p_info fix_state p  in
    let priority = calc_priority p p_info in
    table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    InternalQueue.push internal_queue p priority

  let update = push
    
end


(* solverが保持する動的な状態 *)
module DyState:
sig

  type t
     
  val fix_constraint: t -> G.t -> G.pLavel -> G.cLavel -> unit

end = struct
  
  type t = {fixState: FixState.t;
            queue: PriorityManager.t }


  let tell_predicate_pos_constraint_is_fixed fix_state queue c q =
    if FixState.is_predicate_fixed fix_state q then
      ()
    else if FixState.is_fixable fix_state c q then
      decr (FixState.get_pos_fixable fix_state q)
    else
      let q_unfixable_pos = FixState.get_pos_unfixable fix_state q in
      decr q_unfixable_pos;
      if( !q_unfixable_pos = 0 ) then
        PriorityManager.update queue q fix_state

      else
        ()


  let tell_predicate_neg_constraint_is_fixed fix_state queue c q =
    if FixState.is_predicate_fixed fix_state q then
      ()
    else if FixState.is_fixable fix_state c q then
      decr (FixState.get_neg_fixable fix_state q)
    else
      let q_unfixable_neg = FixState.get_neg_unfixable fix_state q in
      decr q_unfixable_neg;
      if( !q_unfixable_neg = 0 ) then
        PriorityManager.update queue q fix_state

      else
        ()
      
         
         
  let fix_constraint t graph p c =
    let fix_state = t.fixState in
    let queue = t.queue in
      let () = FixState.set_constraint_is_fixed fix_state c in
      let () = tell_predicate_pos_constraint_is_fixed fix_state queue c (G.pos_p graph c) in
      List.iter
        (tell_predicate_neg_constraint_is_fixed fix_state queue c)
        (G.neg_ps graph c)


end
