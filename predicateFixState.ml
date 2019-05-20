module Liq = Type
module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
            
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority
module PredicateInfo = PredicatePriorityQueue.PredicateInfo

                

type state = |Fixed of state  (* pre state *)
             |AllFixable of {fixableNum:int ref
                            ;otherPCount:int ref
                            ;otherPMap: int PMap.t}
             |PartialFixable 
             |ZeroFixable

let state_to_string = function
  |Fixed _ -> "Fixed"
  |AllFixable rc ->
    Printf.sprintf "AllFixable:fixableNum = %d; othere count = %d" !(rc.fixableNum) !(rc.otherPCount)
  |PartialFixable -> "PartialFixable"
  |ZeroFixable -> "ZeroFixable"


let calc_fixable_cons_info  =function
  |Fixed _ -> invalid_arg "calc_priority: already fixed"
  |AllFixable rc ->
    PredicateInfo.{fixLevel = PredicateFixableLevel.all
                  ;otherPCount = Some  !(rc.otherPCount)
                  ;fixableNum = Some !(rc.fixableNum)}
  |PartialFixable ->
    PredicateInfo.{fixLevel = PredicateFixableLevel.partial
                  ;otherPCount = None
                  ;fixableNum = None}

  |ZeroFixable ->
    PredicateInfo.{fixLevel = PredicateFixableLevel.zero
                  ;otherPCount = None
                  ;fixableNum = None}

  
let is_outer_polarity graph p pol =
  ((G.outer_prefered_direction graph p) = Some ConsGraph.PreferedDirection.down && pol = Polarity.pos)
||  ((G.outer_prefered_direction graph p) = Some ConsGraph.PreferedDirection.up && pol = Polarity.neg)
  
                
let calc_p_info graph p state outer_state_opt pol =
  let whole_info = calc_fixable_cons_info state in
  match outer_state_opt with
  |Some outer_state ->
    (* polがouterの向きと一致している時だけ、predicateInfoにout sateの情報を入れる *)
    if is_outer_polarity graph p pol then
      let outer_info = calc_fixable_cons_info outer_state in
      PredicateInfo.{wholeInfo = whole_info
                    ;outerInfo = Some outer_info
                    ;pol = pol
                    ;lavel = p}
    else
      PredicateInfo.{wholeInfo = whole_info
                    ;outerInfo = None
                    ;pol = pol
                    ;lavel = p}    
  |None ->
    PredicateInfo.{wholeInfo = whole_info
                  ;outerInfo = None
                  ;pol = pol
                  ;lavel = p}    



   
   
type t = {posTable: state array
         ;negTable: state array
         ;outerTable: state option array
         
         ;posAffect: int PMap.t array
         ;negAffect: int PMap.t array
         ;outerAffect: int PMap.t array
         }


let table_to_string graph table =
  let _, str = Array.fold_left
                 (fun (i,acc_str) state ->
                   let str = (G.id_of_int graph i)^ " -> " ^ (state_to_string state) in
                   (i+1, acc_str ^ "\n" ^ str))
                 (0, "")
                 table
  in
  str

let outer_table_to_string graph table =
  let _, str = Array.fold_left
                 (fun (i,acc_str) state_opt ->
                   match state_opt with
                   |Some state ->
                     let str = (G.id_of_int graph i)^ " -> " ^ (state_to_string state) in
                     (i+1, acc_str ^ "\n" ^ str)
                   |None ->
                     let str = (G.id_of_int graph i)^ " -> None" in
                     (i+1, acc_str ^ "\n" ^ str))
                 (0, "")
                 table
  in
  str  
  

let to_string graph t =
  "pos table\n"
  ^(table_to_string graph t.posTable)
  ^"\nneg table\n"
  ^(table_to_string graph t.negTable)
  ^"\nouter table\n"
  ^(outer_table_to_string graph t.outerTable)  
      
      

(* これはposTableのみを見ているが、fixedすると、postableもnegtableも Fixedになるので OK*)
let is_fixed t p =
  match t.posTable.(G.int_of_pLavel p) with
  |Fixed _ -> true
  | _ -> false

let isnt_fixed t p = not (is_fixed t p)

let othere_pmap_of_allfixable_pos t p =
  match t.posTable.(G.int_of_pLavel p) with
  |AllFixable {otherPMap = other_pmap} -> Some other_pmap
  | _ -> None

let othere_pmap_of_allfixable_neg t p =
  match t.negTable.(G.int_of_pLavel p) with
  |AllFixable {otherPMap = other_pmap} -> Some other_pmap
  | _ -> None

let othere_pmap_of_allfixable_outer t p =
  match t.outerTable.(G.int_of_pLavel p) with
  |Some (AllFixable {otherPMap = other_pmap}) -> Some other_pmap
  | _ -> None              

(* ************************************************** *)
(* queueにstateを反映させる関数群 *)
(* ************************************************** *)
                   
let push2queue_pos graph q state outer_sate_opt ~change:queue =
  let p_info = calc_p_info graph q state outer_sate_opt Polarity.pos in
  let priority = PriorityQueue.calc_priority queue p_info in
  PriorityQueue.push_pos queue q priority

let push2queue_neg graph q state outer_state_opt ~change:queue =
  let p_info = calc_p_info graph q state outer_state_opt  Polarity.neg in
  let priority = PriorityQueue.calc_priority queue p_info in
  PriorityQueue.push_neg queue q priority  


let update_queue_pos graph q state outer_state_opt ~change:queue =
  let p_info = calc_p_info graph q state outer_state_opt Polarity.pos in
  let priority = PriorityQueue.calc_priority queue p_info in
  PriorityQueue.update_pos queue q priority

let update_queue_neg graph q state outer_state_opt ~change:queue =
  let p_info = calc_p_info graph q state outer_state_opt Polarity.neg in
  let priority = PriorityQueue.calc_priority queue p_info in
  PriorityQueue.update_neg queue q priority  


  

(* fixしたことによる,allfixableの街を変化させる *)
(* ここで、unfixのやつにしか伝播させないという工夫が必要だな、 *)
let fix {posTable = pos_table
        ;negTable =  neg_table
        ;outerTable = outer_table
        ;posAffect =  pos_affect
        ;negAffect =  neg_affect
        ;outerAffect = outer_affect} graph p
        ~may_change:queue =
  let p = G.int_of_pLavel p in
  pos_table.(p) <- Fixed pos_table.(p);
  neg_table.(p) <- Fixed neg_table.(p);
  (match outer_table.(p) with
   |Some outer_state -> outer_table.(p) <- Some (Fixed outer_state)
   |None -> ()
  );
  let () = (PMap.iter
              (fun q i ->
                let q_state_opt = outer_table.(G.int_of_pLavel q) in
                match  q_state_opt with
                |Some (Fixed _)-> ()
                |Some (AllFixable rc) ->
                  (rc.otherPCount := !(rc.otherPCount) - i);
                (* queueへの変更は、pos affect かneg affectの反映の時に行われるのでここではしない *)
                |_ -> ())
              outer_affect.(p) )
  in  
  let () = (PMap.iter
              (fun q i ->
                let q_state = pos_table.(G.int_of_pLavel q) in
                match  q_state with
                |Fixed _-> ()
                |AllFixable rc ->
                  let q_outer_state_opt = outer_table.(G.int_of_pLavel q) in
                  (rc.otherPCount := !(rc.otherPCount) - i);
                  push2queue_pos graph q q_state q_outer_state_opt ~change:queue
                |_ -> ())
              pos_affect.(p) )
  in
  let () = (PMap.iter
              (fun q i ->
                let q_state = neg_table.(G.int_of_pLavel q) in
                match  q_state with                    
                |Fixed _ ->  ()
                |AllFixable  rc ->
                  let q_outer_state_opt = outer_table.(G.int_of_pLavel q) in                  
                  (rc.otherPCount := !(rc.otherPCount) - i);
                  push2queue_neg graph q q_state q_outer_state_opt ~change:queue                  
                |_ -> ())
              neg_affect.(p) )      
  in
  ()


(* 
   unfixが呼ばれた時の状態:
   　pos_table.(p) = Fixed pre_state  
   neg_table.(p) = Fixed pre_state
   outer_table.(p) = Fixed pre_state
   pos_affet.(p) = <pがfixした時の状態を保持している>
   neg_affect, outer_affectも同様
*)
let unfix {posTable = pos_table
          ;negTable =  neg_table
          ;outerTable = outer_table
          ;posAffect =  pos_affect
          ;negAffect =  neg_affect
          ;outerAffect = outer_affect} graph p
          ~may_change:queue =
  let p = G.int_of_pLavel p  in
  let () = (PMap.iter
              (fun q i ->
                let q_state_opt = outer_table.(G.int_of_pLavel q) in
                match  q_state_opt with
                |Some (Fixed _)-> ()
                |Some (AllFixable rc) ->
                  (rc.otherPCount := !(rc.otherPCount) + i);
                (* queueへの変更は、pos affect かneg affectの反映の時に行われるのでここではしない *)
                |_ -> ())
              outer_affect.(p) )

  in
  let () = (PMap.iter
              (fun q i ->
                let q_state = pos_table.(G.int_of_pLavel q) in
                match  q_state with
                |Fixed _-> ()
                |AllFixable rc ->
                  let q_outer_state_opt = outer_table.(G.int_of_pLavel q) in
                  (rc.otherPCount := !(rc.otherPCount) + i);
                  push2queue_pos graph q q_state q_outer_state_opt ~change:queue
                |_ -> ())
              pos_affect.(p) )
  in
  let () = (PMap.iter
              (fun q i ->
                let q_state = neg_table.(G.int_of_pLavel q) in
                match  q_state with                    
                |Fixed _ ->  ()
                |AllFixable  rc ->
                  let q_outer_state_opt = outer_table.(G.int_of_pLavel q) in                  
                  (rc.otherPCount := !(rc.otherPCount) - i);
                  push2queue_neg graph q q_state q_outer_state_opt ~change:queue                  
                |_ -> ())
              neg_affect.(p) )        
  in      
  match pos_table.(p), neg_table.(p) with
  |Fixed pos_pre_state, Fixed neg_pre_state ->
    pos_table.(p) <- pos_pre_state;
    neg_table.(p) <- neg_pre_state
  |_ -> assert false


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

let update_affect_if_all_fixable affect p updated_state =
  match updated_state with
  |AllFixable rc -> update_affect affect p rc.otherPMap
  | _ -> ()

  
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

let fixable_level_to_fix_state fixable_level fixable_num (calc_othere_p: unit -> int PMap.t) =
  if fixable_level = PredicateFixableLevel.partial then
    PartialFixable
  else if fixable_level = PredicateFixableLevel.zero then
    ZeroFixable
  else if fixable_level = PredicateFixableLevel.all then
    let othere_unknown_map = calc_othere_p () in
    let unknown_count = count_unknown othere_unknown_map in
    AllFixable {fixableNum = ref fixable_num
               ;otherPCount = ref unknown_count
               ;otherPMap = othere_unknown_map}
  else
    assert false
    

(* update pos table by fixable level (and othere auxiliary info) *)
let pos_update' t p fixable_level fixable_num calc_ohere_p =
  let pos_table = t.posTable in
  match pos_table.(G.int_of_pLavel p) with
  |Fixed _ -> invalid_arg "pos_update:attempt to update fixed predicate "
  |AllFixable rc ->
    remove_affect t.posAffect p rc.otherPMap;
    let new_state = fixable_level_to_fix_state fixable_level fixable_num calc_ohere_p in
    let () = pos_table.(G.int_of_pLavel p) <- new_state in
    let () = update_affect_if_all_fixable t.posAffect p new_state in    
    new_state
  |PartialFixable |ZeroFixable ->
    let new_state = fixable_level_to_fix_state fixable_level fixable_num calc_ohere_p in
    let () = pos_table.(G.int_of_pLavel p) <- new_state in
    let () = update_affect_if_all_fixable t.posAffect p new_state in        
    new_state

    
(* update neg table by fixable level (and othere auxiliary info) *)
let neg_update' t p fixable_level fixable_num calc_other_p =
  let neg_table = t.negTable in
  match neg_table.(G.int_of_pLavel p) with
  |Fixed _ -> invalid_arg "neg_update:attempt to update fixed predicate "
  |AllFixable rc ->
    remove_affect t.negAffect p rc.otherPMap;
    let new_state = fixable_level_to_fix_state fixable_level fixable_num calc_other_p in
    let () = neg_table.(G.int_of_pLavel p) <- new_state in
    let () = update_affect_if_all_fixable t.negAffect p new_state in    
    new_state
  |PartialFixable |ZeroFixable ->
    let new_state = fixable_level_to_fix_state fixable_level fixable_num calc_other_p in
    let () = neg_table.(G.int_of_pLavel p) <- new_state in
    let () = update_affect_if_all_fixable t.negAffect p new_state in
    new_state

(* update outer table by fixable level (and othere auxiliary info) *)
let outer_update' t p fixable_level fixable_num calc_other_p =
  let outer_table = t.outerTable in
  match outer_table.(G.int_of_pLavel p) with
  |Some (Fixed _) -> invalid_arg "neg_update:attempt to update fixed predicate "
  |Some (AllFixable rc) ->
    remove_affect t.outerAffect p rc.otherPMap;
    let new_state = fixable_level_to_fix_state fixable_level fixable_num calc_other_p in
    let () = outer_table.(G.int_of_pLavel p) <- Some new_state in
    let () = update_affect_if_all_fixable t.outerAffect p new_state in        
    new_state
  |Some PartialFixable |Some ZeroFixable ->
    let new_state = fixable_level_to_fix_state fixable_level fixable_num calc_other_p in
    let () = outer_table.(G.int_of_pLavel p) <- Some new_state in
    let () = update_affect_if_all_fixable t.outerAffect p new_state in            
    new_state
  |None -> invalid_arg "outer_update: try to update outer state of predicate without outer constraints "

  
let pos_update t graph p
               ~pos_info:(fixable_level, calc_othere_p, fixable_num)
               ~outer_info:outer_info
               ~change:queue
  =
  match outer_info with
  |Some (fixable_level_out, calc_othere_out, fixable_num_out) ->
    let updated_state_pos = pos_update' t p fixable_level fixable_num calc_othere_p in
    let updated_state_outer = outer_update' t p fixable_level_out fixable_num_out calc_othere_out in
    update_queue_pos graph p updated_state_pos (Some updated_state_outer) ~change:queue
  |None ->
    let updated_state_pos = pos_update' t p fixable_level fixable_num calc_othere_p in
    update_queue_pos graph p updated_state_pos None ~change:queue

    
let neg_update t graph p
               ~neg_info:(fixable_level, calc_othere_p, fixable_num)
               ~outer_info:outer_info
               ~change:queue
  =
  match outer_info with
  |Some (fixable_level_out, calc_othere_out, fixable_num_out) ->
    let updated_state_neg = neg_update' t p fixable_level fixable_num calc_othere_p in
    let updated_state_outer = outer_update' t p fixable_level_out fixable_num_out calc_othere_out in
    update_queue_neg graph p updated_state_neg (Some updated_state_outer) ~change:queue
  |None ->
    let updated_state_neg = neg_update' t p fixable_level fixable_num calc_othere_p in
    update_queue_neg graph p updated_state_neg None ~change:queue        
    
  
module Constructor = struct

  let dummy_state = ZeroFixable
  
  let create size = {posTable = Array.make size dummy_state
                    ;negTable = Array.make size dummy_state
                    ;outerTable = Array.make size None
                    ;posAffect = Array.make size PMap.empty
                    ;negAffect = Array.make size PMap.empty
                    ;outerAffect = Array.make size PMap.empty
                    }

  let outer_register t p fixable_level_out fixable_num_out calc_other_out =
    let outer_table = t.outerTable in
    let new_state = fixable_level_to_fix_state fixable_level_out fixable_num_out calc_other_out in
    let () = outer_table.(G.int_of_pLavel p) <- Some new_state in
    let () = update_affect_if_all_fixable t.outerAffect p new_state in            
    ()    

  let pos_registor = pos_update
    
  let neg_registor = neg_update

end
