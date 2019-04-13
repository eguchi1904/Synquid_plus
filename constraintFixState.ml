module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority

module PFixState = PredicateFixState

module PFixableConstraintCounter = PredicateFixableCounter
         

type t = {isFix: bool array
         ;unknown_p_count: int array           
         ;unknown_up_p_count: int array
         }

let is_fixed t c = t.isFix.(G.int_of_cLavel c)

let isnt_fixed t c = not (is_fixed t c)


(* ここを拡張する必要があるわけだ *)
let fix t c = 
  (t.isFix.(G.int_of_cLavel c) <- true)


let is_zero_unknown t c =
  t.unknown_p_count.(G.int_of_cLavel c) = 0

let is_only_upp_p t c =
  t.unknown_p_count.(G.int_of_cLavel c)  =
    t.unknown_up_p_count.(G.int_of_cLavel c)
  

  
let prop_p_fix_to_c t graph p c =
  let c = G.int_of_cLavel c in  
  if G.is_upp_p graph p then
    begin
      (t.unknown_p_count.(c) <- t.unknown_p_count.(c)  - 1);
          (t.unknown_up_p_count.(c) <- t.unknown_up_p_count.(c)  - 1);
        end
  else
    (t.unknown_p_count.(c) <- t.unknown_p_count.(c)  - 1)

    
let prop_p_fix t graph p =
  (* この時点でunfixなものに伝播する *)
  let () = List.iter
             (prop_p_fix_to_c t graph p)
             (List.filter (isnt_fixed t) (G.pos_cs graph p))
  in
  let () = List.iter
             (prop_p_fix_to_c t graph p)
             (List.filter (isnt_fixed t) (G.neg_cs graph p))
  in
  ()
        
          

