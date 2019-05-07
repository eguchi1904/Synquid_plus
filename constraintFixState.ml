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

let unfix_cs_around_p t graph p =
  let unfix_pos_cs = (G.pos_cs graph p)
                     |> List.filter (isnt_fixed t)
  in
  let unfix_neg_cs = (G.neg_cs graph p)
                     |> List.filter (isnt_fixed t)
                     |> List.filter (fun c -> not (List.mem c unfix_pos_cs))
  in
  unfix_pos_cs@unfix_neg_cs
  
  
  


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
      (t.unknown_p_count.(c) <- t.unknown_p_count.(c) - 1);
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


let create_p_counts up_ps graph  =
  let c_num = G.cNode_num graph in  
  let p_count = Array.make c_num 0 in
  let up_p_count = Array.make c_num 0 in
  let () = G.fold_c
             (fun c_lav () ->
               let c = G.cons_of_cLavel graph c_lav in
               let unknown_ps = Constraint.unknown_p_in_simple_cons c in
               let unknown_up_ps = S.inter unknown_ps up_ps in
               (p_count.(G.int_of_cLavel c_lav) <- S.cardinal unknown_ps);
               (up_p_count.(G.int_of_cLavel c_lav) <- S.cardinal unknown_up_ps))
             graph
             ()
  in
  (p_count, up_p_count)
      


  

let create up_ps graph =
  let p_count, up_p_count = create_p_counts up_ps graph in
  {isFix = Array.make (G.cNode_num graph) false
  ;unknown_p_count = p_count
  ;unknown_up_p_count = up_p_count
  }

  
  

