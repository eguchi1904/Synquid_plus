open Extensions
open Constraint

   
module Liq = Type
module Heap = Core.Heap         (* heapのためだけに、Core依存 *)

exception InValid of Constraint.simple_cons
exception UnSat of Constraint.simple_cons

(* represent positive occurence, negative occurence of predicate in constraint *)

                     
                     
module Polarity:
sig
  type t = private int
  val pos: t
  val neg: t
end = struct
  type t = int
  let pos = 1
  let neg = 0                   (*  negativeのが優先順位高いかな *)
end

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



(*
 type fixableLevle 
  = |Already_Fixed
    |AllFixable of int
    |PartialFix
    |ZeroFix

  *)
module PredicateFixableLevel:
sig
  type t = private int 
  val all: t
  val partial: t        (* partial is_hinted *)
  val zero:  t           (* zero is_hinted *)
end = struct
  type t =  int
  let all  = 0
  let partial  = 1
  let zero  = 2
end

    
module Priority = struct
  (* the most important factor is fixable level *)
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
    
end  = struct
  
                  
  module InternalQueue:
  sig

    type t = private Priority.t Heap.t

    val pop: t ->  Priority.t option

    val push: t -> Priority.t -> unit

  end = struct

    type t = Priority.t Heap.t

    let pop heap =
      match Heap.pop heap with
      |None -> None
      |Some priority -> Some priority

      
    let push heap priority= Heap.add heap priority

  end

      
  type t = {table: Priority.t array
           ;internalQueue: InternalQueue.t
           }


  let rec pop ({table = table; internalQueue = internal_queue} as queue) =
    match InternalQueue.pop internal_queue with
    |None -> None
    |Some priority ->
      let p = priority.Priority.lavel in
      let priority' =  table.(G.int_of_pLavel p) in
      if priority = priority' then
        (* insert dummy priority into table *)
        let () = table.(G.int_of_pLavel p) <-  {fixLevel = PredicateFixableLevel.fixed
                                               ;fixableNum = priority.fixableNum
                                               ;pol =  priority.pol
                                               ;lavel = priority.lavel}
        in
        Some (p, priority)
      else                        (* updated old element *)
        pop queue


  let push {table = table; internalQueue = internal_queue} p priority = 
    table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    InternalQueue.push internal_queue priority

  let update = push
      
      
end


module PFixState = struct

  type state = |Fixed
               |AllFixable of int
               |PartialFixable
               |ZeroFixable
               
  
  type t = {posTable: state array
           ;negTable: state array
             
           ;posAffect: (G.pLavel * int) list array
           ;negAffect: (G.pLavel * int) list array
           }           



    let fix {posTable = pos_table
            ;negTable =  neg_table
            ;posAffect =  pos_affect
            ;negAffect =  neg_affect } p =
      let p = G.int_of_pLavel p in
      let () = (List.iter
                  (fun (q,i) ->
                    let q = G.int_of_pLavel q in
                    match  pos_table.(q) with
                    |Fixed -> ()
                    |AllFixable n -> pos_table.(q) <-  AllFixable (n - i);
                    |_ -> assert false)
                  pos_affect.(p) )
      in
      let () = (List.iter
                  (fun (q,i) ->
                    let q = G.int_of_pLavel q in
                    match  neg_table.(q) with
                    |Fixed -> ()
                    |AllFixable n -> neg_table.(q) <-  AllFixable (n - i);
                    |_ -> assert false)
                  neg_affect.(p) )      
      in
      pos_table.(p) <- Fixed;
      neg_table.(p) <- Fixed
      
  end
    


   
(* Fix information (dynamic) *)
module PFixableConstraintCounter:
sig
  
 type fixRatio = {fixable: int ref ; unfixable: int ref }


 (* !isFIx = trueの時、他のレコードは無意味な値 *)
 type pInfo = {posRatio: fixRatio
              ;negRatio: fixRatio
               }               

  type t 

         (* val decr_pos_unfix: t -> G.pLavel -> unit *)

         (* val decr_neg_unfix: t -> G.pLavel -> unit *)
     

    
end= struct
  

  type fixRatio = {fixable: int ref ; unfixable: int ref } 

                
  let to_fixable_level  {fixable = fixable; unfixable =unfixable} =
    if !unfixable = 0 then
      PredicateFixableLevel.all
    else if !fixable >  0 then
      PredicateFixableLevel.partial 
    else
      PredicateFixableLevel.zero
    

  (* !isFIx = trueの時、他のレコードは無意味な値 *)
  type pInfo ={posRatio: fixRatio
              ;negRatio: fixRatio
              }               

          
  type t =  pInfo array

         

end

   
module CFixState = struct
  
  type cInfo = {isFix: bool ref
               ;unknown_p_count:  int ref
               ;unknown_up_p_count: int ref
               }
             


  type t = {isFix: bool array
           ;unknown_p_count: int array           
           ;unknown_up_p_count: int array
           }

  let is_fixed t c = t.isFix.(G.int_of_cLavel c)

end


module Fixablility = struct

  (* これはconstraint.mlに写しても良いかもな *)
  type bound = |UpBound of {env: Liq.env; vars: S.t; bound: Formula.t }
               |LowBound of {env: Liq.env; vars: S.t; bound: Formula.t }


  type t = |UnBound of int ref
           |Bound of (int ref * bound)
                   
  
end


module FixablilityManager = struct
  
  exception Cons_pred_mismatch
          
  type t = {table: ((G.cLavel * G.pLavel), Fixablility.t ) Hashtbl.t
           ;affect: ((G.cLavel * G.pLavel) list) array }
  
end
                          
                  
                  
module DyState:
sig

  type t
     
  (* val fix_constraint: t -> G.t -> G.pLavel -> G.cLavel -> unit *)

end = struct
  
  type t = {fixability: FixablilityManager.t
           ;pFixState: PFixState.t
           ;cFixState: CFixState.t
           ;queue: PriorityQueue.t
           }


  (* pをfixする *)
  let fix t graph p pol =
    

    


  let tell_predicate_pos_constraint_is_fixed fix_state queue c q =
    if FixState.is_predicate_fixed fix_state q then
      ()
    else if FixState.is_fixable fix_state c q then (* fixableが他のpでfixした *)
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


      
        (* let tell_constraint_pos_predicate_is_fixed t graph p c = *)
    
    


end
