module Liq = Type
module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
            
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority

                

type state = |Fixed of state  (* pre state *)
             |AllFixable of {fixableNum:int ref
                            ;otherPCount:int ref
                            ;otherPMap: int PMap.t}
             |PartialFixable 
             |ZeroFixable

let calc_priority state pol p =
  match state with
  |Fixed _ -> invalid_arg "calc_priority: already fixed"
  |AllFixable rc ->
    Priority.{fixLevel = PredicateFixableLevel.all
             ;otherPCount = !(rc.otherPCount)
             ;fixableNum = !(rc.fixableNum)
             ;pol = pol
             ;lavel = p
    }
  |PartialFixable ->
    Priority.{fixLevel = PredicateFixableLevel.partial
             ;otherPCount = 0
             ;fixableNum = 0  (* dummy *)
             ;pol = pol
             ;lavel = p
    }
  |ZeroFixable ->
    Priority.{fixLevel = PredicateFixableLevel.zero
             ;otherPCount = 0
             ;fixableNum = 0  (* dummy *)
             ;pol = pol
             ;lavel = p
    }      

   
   
type t = {posTable: state array
         ;negTable: state array
         
         ;posAffect: int PMap.t array
         ;negAffect: int PMap.t array

         }           


let is_fixed t p =
  match t.posTable.(G.int_of_pLavel p) with
  |Fixed _ -> true
  | _ -> false

let isnt_fixed t p = not (is_fixed t p)


                   
(* この時点で、pをfixしたことによる、fixableLevelの変化は反映されていないといけない *)
(* fixしたことによる,allfixableの街を変化させる *)
let fix {posTable = pos_table
        ;negTable =  neg_table
        ;posAffect =  pos_affect
        ;negAffect =  neg_affect } p
        ~may_change:queue =
  let p = G.int_of_pLavel p in
  let () = (PMap.iter
              (fun q i ->
                let q_state = pos_table.(G.int_of_pLavel q) in
                match  q_state with
                |Fixed _-> ()
                |AllFixable rc ->
                  (rc.otherPCount := !(rc.otherPCount) - i);
                  calc_priority q_state Polarity.pos q
                  |> PriorityQueue.push_pos queue q 
                |_ -> ())
              pos_affect.(p) )
  in
  let () = (PMap.iter
              (fun q i ->
                let q_state = neg_table.(G.int_of_pLavel q) in
                match  q_state with                    
                |Fixed _ ->  ()
                |AllFixable  rc ->
                  (rc.otherPCount := !(rc.otherPCount) - i);
                  calc_priority q_state Polarity.neg q
                  |> PriorityQueue.push_neg queue q                       
                |_ -> ())
              neg_affect.(p) )      
  in
  pos_table.(p) <- Fixed pos_table.(p);
  neg_table.(p) <- Fixed neg_table.(p) 

(* この時点で、pをunfixしたことによる、fixableLevelの変化は反映されていないといけない *)
let unfix {posTable = pos_table
          ;negTable =  neg_table
          ;posAffect =  pos_affect
          ;negAffect =  neg_affect } p
          ~may_change:queue =
  let p = G.int_of_pLavel p  in
  let () = (PMap.iter
              (fun q i ->
                let q_state = pos_table.(G.int_of_pLavel q) in
                match  q_state with                      
                |Fixed _-> ()
                |AllFixable rc ->
                  (rc.otherPCount := !(rc.otherPCount) + i);
                  calc_priority q_state Polarity.pos q
                  |> PriorityQueue.push_pos queue q 
                |_ -> assert false)
              pos_affect.(p) )
  in
  let () = (PMap.iter
              (fun q i ->
                let q_state = neg_table.(G.int_of_pLavel q) in
                match  q_state with                                        
                |Fixed _ ->  ()
                |AllFixable rc ->
                  (rc.otherPCount := !(rc.otherPCount) + i);
                  calc_priority q_state Polarity.neg q
                  |> PriorityQueue.push_neg queue q                                             
                |_ -> assert false)
              neg_affect.(p) )      
  in      
  match pos_table.(p), neg_table.(p) with
  |pos_pre_state, neg_pre_state ->
    pos_table.(p) <- pos_pre_state;
    neg_table.(p) <- neg_pre_state


let list_unfixed state_table p adj_list =
  List.fold_left
    (fun acc q ->
      match state_table.(G.int_of_pLavel q) with
      |Fixed _ -> acc
      |AllFixable _ |PartialFixable |ZeroFixable -> q::acc
    )
    []
    adj_list

  
let update_affect affect p othere_unknown_map =
  PMap.iter
    (fun q i -> affect.(G.int_of_pLavel q) <- PMap.add p i affect.(G.int_of_pLavel q) )
    othere_unknown_map

  
let remove_affect affect p othere_unknown_map =
  PMap.iter
    (fun q i -> affect.(G.int_of_pLavel q) <- PMap.remove p affect.(G.int_of_pLavel q) )
    othere_unknown_map

  
let sub_affect affect p removing_othere_unknown_map =
  PMap.iter
    (fun q i ->
      let q_affect = affect.(G.int_of_pLavel q) in
      let p_i = PMap.find p q_affect in
      let q_affect' = PMap.add p (p_i - i) q_affect in 
      affect.(G.int_of_pLavel q) <- q_affect'
    )
    removing_othere_unknown_map

let sub_unknown_map map1 map2 =
  PMap.union
    (fun x i1 i2 -> Some (i1 - i2))
    map1
    map2

let count_unknown unknown_map =
  PMap.fold
    (fun _ i acc -> i+ acc)
    unknown_map
    0      
  

(* partial -> allfiable
       zero -> allfixable
       にupdateするときは特別, affect mapを必要とするため *)       
let pos_update2allfixable' t p fixable_num (othere_unknown_map: int PMap.t) = 
  let pos_table = t.posTable in
  match pos_table.(G.int_of_pLavel p) with
  |Fixed _ | AllFixable _ ->
    invalid_arg "pos_update2allfixable: decreasing update"
  |PartialFixable |ZeroFixable ->
    let unknown_count = count_unknown othere_unknown_map in
    let state = AllFixable {fixableNum = ref fixable_num
                           ;otherPCount = ref unknown_count
                           ;otherPMap = othere_unknown_map}
    in
    pos_table.(G.int_of_pLavel p) <- state;
    (update_affect t.posAffect p othere_unknown_map);
    state
    
    
let neg_update2allfixable' t p fixable_num (othere_unknown_map: int PMap.t) = 
  let neg_table = t.negTable in
  match neg_table.(G.int_of_pLavel p) with
  |Fixed _ | AllFixable _ ->
    invalid_arg "neg_update2allfixable: decreasing update"
  |PartialFixable |ZeroFixable ->
    let unknown_count = count_unknown othere_unknown_map in
    let state = AllFixable {fixableNum = ref fixable_num
                           ;otherPCount = ref unknown_count
                           ;otherPMap = othere_unknown_map}
    in
    neg_table.(G.int_of_pLavel p) <- state;
    (update_affect t.negAffect p othere_unknown_map);
    state
    
    
let pos_update2allfixable t p (othere_unknown_map: int PMap.t)
                          fixable_num ~change:queue =
  let updated_state = pos_update2allfixable' t p fixable_num othere_unknown_map in
  let updated_priority = calc_priority updated_state Polarity.pos p in
  PriorityQueue.update_pos queue p updated_priority
  
  

let neg_update2allfixable t p (othere_unknown_map: int PMap.t)
                          fixable_num ~change:queue =
  let updated_state = neg_update2allfixable' t p fixable_num othere_unknown_map in
  let updated_priority = calc_priority updated_state Polarity.neg p in
  PriorityQueue.update_neg queue p updated_priority
  
  
(* backtraceでこうなることもあるね、
     affectから自分を消してから変更する*)
(* let pos_update_from_allfixable t p fixable_level = *)
(*   let pos_table = t.posTable in *)
(*   match pos_table.(G.int_of_pLavel p) with *)
(*   |AllFixable (n, map) -> *)
(*     remove_affect t.posAffect p map; *)
(*     pos_table.(G.int_of_pLavel p) <- fixable_level *)
(*   |_ -> invalid_arg "pos_update_from_allfixable: not allfixable" *)
(* 上がるのにも下がるのにも対応する backtraceがあるので *)

let update_table table p fixable_level =
  if fixable_level = PredicateFixableLevel.partial then
    let () = table.(G.int_of_pLavel p) <- PartialFixable in
    PartialFixable
  else if fixable_level = PredicateFixableLevel.zero then
    let () = table.(G.int_of_pLavel p) <- ZeroFixable in
    ZeroFixable
  else if fixable_level = PredicateFixableLevel.all then
    invalid_arg "update: use update2allfixable!"            
  else
    assert false
  
let pos_update' t p fixable_level =
  let pos_table = t.posTable in
  match pos_table.(G.int_of_pLavel p) with
  |Fixed _ -> invalid_arg "pos_update:attempt to update fixed predicate "
  |AllFixable rc ->
    remove_affect t.posAffect p rc.otherPMap;
    update_table pos_table p fixable_level
  |PartialFixable |ZeroFixable ->
    update_table pos_table p fixable_level


let neg_update' t p fixable_level =
  let neg_table = t.negTable in
  match neg_table.(G.int_of_pLavel p) with
  |Fixed _ -> invalid_arg "neg_update:attempt to update fixed predicate "
  |AllFixable rc ->
    remove_affect t.negAffect p rc.otherPMap;
    update_table neg_table p fixable_level
  |PartialFixable |ZeroFixable ->
    update_table neg_table p fixable_level

let pos_update t p fixable_level
               ~change:queue = 
  let _ = (pos_update' t p fixable_level) in
  let priority = Priority.{ fixLevel = fixable_level
                           ;otherPCount = 0
                           ;fixableNum = 0 (* dummy *)
                           ;pol = Polarity.pos
                           ;lavel = p
                 }
  in
  PriorityQueue.update_pos queue p priority

let neg_update t p fixable_level
               ~change:queue = 
  let _ = (neg_update' t p fixable_level) in
  let priority = Priority.{ fixLevel = fixable_level
                           ;otherPCount = 0
                           ;fixableNum = 0 (* dummy *)
                           ;pol = Polarity.neg
                           ;lavel = p
                 }
  in
  PriorityQueue.update_neg queue p priority


  
let pos_decr_othere_p_form_allfixable' t p (rm_map:int PMap.t) = 
  let pos_table = t.posTable in
  match pos_table.(G.int_of_pLavel p) with
  |Fixed _ |PartialFixable |ZeroFixable ->
    invalid_arg "neg_decr_othere_p_form_allfixable: not allfixable"
  |AllFixable rc ->
    (sub_affect t.posAffect p rm_map);
    let removing_unknown_count = count_unknown rm_map in
    let new_state =
      AllFixable {fixableNum = ref !(rc.fixableNum)
                 ;otherPCount = ref (!(rc.otherPCount) - removing_unknown_count)
                 ;otherPMap = sub_unknown_map rc.otherPMap rm_map}
    in
    let () = pos_table.(G.int_of_pLavel p) <- new_state in
    new_state

    
let neg_decr_othere_p_form_allfixable' t p (rm_map:int PMap.t) =
  let neg_table = t.negTable in
  match neg_table.(G.int_of_pLavel p) with
  |Fixed _ |PartialFixable |ZeroFixable ->
    invalid_arg "neg_decr_othere_p_form_allfixable: not allfixable"
  |AllFixable rc ->
    (sub_affect t.negAffect p rm_map);
    let removing_unknown_count = count_unknown rm_map in
    let new_state =
      AllFixable {fixableNum = ref !(rc.fixableNum)
                 ;otherPCount = ref (!(rc.otherPCount) - removing_unknown_count)
                 ;otherPMap = sub_unknown_map rc.otherPMap rm_map}
    in
    let () = neg_table.(G.int_of_pLavel p) <- new_state in
    new_state

    
let pos_decr_othere_p_form_allfixable t p (rm_map:int PMap.t) ~change:queue =
  let updated_sate = pos_decr_othere_p_form_allfixable' t p rm_map in
  let updated_priority = calc_priority updated_sate Polarity.pos p in
  PriorityQueue.update_pos queue p updated_priority

  
let neg_decr_othere_p_form_allfixable t p (rm_map:int PMap.t) ~change:queue =
  let updated_sate = pos_decr_othere_p_form_allfixable' t p rm_map in
  let updated_priority = calc_priority updated_sate Polarity.neg p in
  PriorityQueue.update_pos queue p updated_priority        
  
  

  
module Constructor = struct

  let dummy_state = ZeroFixable
  
  let create size = {posTable = Array.make size dummy_state
                    ;negTable = Array.make size dummy_state
                    ;posAffect = Array.make size PMap.empty
                    ;negAffect = Array.make size PMap.empty
                    }

  let pos_registor t p fixable_level ~change:queue =
    let state = update_table t.posTable p fixable_level in (* fixable_level = allの時はinvalid *)
    let priority = calc_priority state Polarity.pos p in
    PriorityQueue.push_pos queue p priority

    
    
  let neg_registor t p fixable_level ~change:queue =
    let state = update_table t.negTable p fixable_level in (* fixable_level = allの時はinvalid *)
    let priority = calc_priority state Polarity.neg p in
    PriorityQueue.push_pos queue p priority

  let pos_registor_allfixable t p (othere_unknown_map: int PMap.t) fixable_num
                              ~change:queue
    = 
    let unknown_count = count_unknown othere_unknown_map in
    let state = AllFixable {fixableNum = ref fixable_num
                           ;otherPCount = ref unknown_count
                           ;otherPMap = othere_unknown_map}
    in
    let () = t.posTable.(G.int_of_pLavel p) <- state in
    let () = update_affect t.posAffect p othere_unknown_map in
    let priority = calc_priority state Polarity.pos p in
    PriorityQueue.push_pos queue p priority    


    
  let neg_registor_allfixable t p (othere_unknown_map: int PMap.t) fixable_num 
                              ~change:queue
    =
    let unknown_count = count_unknown othere_unknown_map in
    let state = AllFixable {fixableNum = ref fixable_num
                           ;otherPCount = ref unknown_count
                           ;otherPMap = othere_unknown_map}
    in
    let () = t.negTable.(G.int_of_pLavel p) <- state in
    let () = update_affect t.negAffect p othere_unknown_map in
    let priority = calc_priority state Polarity.neg p in
    PriorityQueue.push_pos queue p priority        



end
