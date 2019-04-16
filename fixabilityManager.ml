module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
module CMap =  ConsGraph.CMap
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority

module PFixState = PredicateFixState

module PFixableConstraintCounter = PredicateFixableCounter

module CFixState = ConstraintFixState
                 
                 
exception Cons_pred_mismatch of string
                              
type t = {table: ((G.pLavel * G.cLavel), Fixability.t Stack.t) Hashtbl.t
         ;affect: ((G.pLavel * G.cLavel), G.pLavel list) Hashtbl.t }

let of_string graph t =
  Hashtbl.fold
    (fun (p,c) stack acc_str ->
      try
        let fixability = Stack.top stack  in
        let str = Printf.sprintf "\n(%s, c:%d) -> %s" (G.id_of_pLavel graph p) (G.int_of_cLavel c) (Fixability.of_string fixability) in
        (acc_str^str)
      with
        _ -> acc_str
    )
  t.table
  ""
      

let is_fixable t p c =
  let stack = Hashtbl.find t.table (p,c) in
  Fixability.is_fixable (Stack.top stack )

(* (p,c) ->q,q',...
     pがfixした時に,constraint cでpを待っているpredicate
 *)

(* p,c must be fixable *)
let count_other_unknown_in_c t graph assign p c =
  let fixability =  Stack.top (Hashtbl.find t.table (p, c)) in
  Fixability.count_othere_p fixability graph assign
  

let count_other_unknown_in_cs t graph assign p cs = 
  List.fold_left
    (fun acc_map c ->
      let pmap = count_other_unknown_in_c t graph assign p c in
      PMap.union (fun q i i' -> Some (i+i')) pmap acc_map)
    PMap.empty
    cs

  
let count_other_unknown_in_unfix_cs t graph assign cfix_state pol p =
  if pol = Polarity.pos then
    (G.pos_cs graph p)
    |> List.filter (fun c -> not (CFixState.is_fixed cfix_state c))
    |> count_other_unknown_in_cs t graph assign  p

  else
    (G.neg_cs graph p)
    |> List.filter (fun c -> not (CFixState.is_fixed cfix_state c))
    |> count_other_unknown_in_cs t graph assign  p      
  
  
let add_affect affect p c q =
  match Hashtbl.find_opt affect (p,c) with
  |Some l -> Hashtbl.replace affect (p,c) (q::l)
  |None -> Hashtbl.add affect (p,c) [q]

let update_affect t p c wait_ps = (* p,cを解くためには、wait_psが必要等情報をadd *)
  PSet.iter
    (fun q -> add_affect t.affect q c p)
    wait_ps
  
  
let decr_wait_num t assign graph cfix_state q c 
                  ~may_change:(pfixable_counter, pfix_state, queue) =
  let fixability_stack = Hashtbl.find t.table (q,c) in
  let fixability = Stack.top fixability_stack in
  match Fixability.decr_wait_num assign graph q c ~change:fixability with
  |Some (new_fixability, new_wait_ps) ->
    (Stack.push new_fixability fixability_stack);
    (update_affect t q c new_wait_ps);
    (* (q c)がFixableになった時の処理 *)
    (match new_fixability with
     |Fixability.Fixable (pol,_) ->
       let calc = (fun () ->
           count_other_unknown_in_unfix_cs t graph assign cfix_state pol q)
       in
       (* qがallfixableになったら、calcを呼び出してothereUnknownの数 を集計する *)
       PFixableConstraintCounter.unfixable2fixable pfixable_counter q pol calc
                                                   ~may_change:(pfix_state, queue)
     |_ -> ())
  |None -> ()
         

let tell_constraint_predicate_is_fixed t graph assign cfix_state p c
                                       ~may_change:(pfixable_counter, pfix_state, queue) =
  List.iter
    (fun q -> decr_wait_num t assign graph cfix_state q c 
                            ~may_change:(pfixable_counter, pfix_state, queue)
    )
    (List.filter (PFixState.isnt_fixed pfix_state) (Hashtbl.find t.affect (p,c)) )


  
let tell_predicate_constraint_is_fixed t graph assign cfix_state c q pol
                                       ~may_change:(pfixable_counter, pfix_state, queue) =
  if is_fixable t q c then
    let gen_rm_pmap =(fun () -> count_other_unknown_in_c t graph assign q c) in
    PFixableConstraintCounter.remove_fixable pfixable_counter q pol gen_rm_pmap
                                             ~may_change:(pfix_state, queue)
  else
    let gen_pmap = (fun () -> count_other_unknown_in_unfix_cs
                                t graph assign cfix_state pol q)
    in
    PFixableConstraintCounter.remove_unfixable pfixable_counter q pol gen_pmap
                                               ~may_change:(pfix_state, queue)


(* この時点でcfix_stateは最新のものになっている必要がある *)
let tell_related_predicate_constraint_is_fixed t graph assign cfix_state p c 
                                               ~may_change:(pfixable_counter, pfix_state, queue) =
  let isnt_fix q = (PFixState.isnt_fixed pfix_state q && q <> p) in
  let unfixed_pos_p = (List.filter isnt_fix (G.pos_ps graph c)) in    
  let () =
    List.iter
      (fun q ->
        tell_predicate_constraint_is_fixed t graph assign cfix_state c q Polarity.pos
                                           ~may_change:(pfixable_counter, pfix_state, queue))
      unfixed_pos_p
  in
  let unfixed_neg_p = (List.filter isnt_fix (G.neg_ps graph c)) in
  List.iter
    (fun q -> tell_predicate_constraint_is_fixed t graph assign cfix_state c q Polarity.neg
                                                 ~may_change:(pfixable_counter, pfix_state, queue))
    unfixed_neg_p
  
  
  
let try_to_fix t assign p c =
  let fixability_stack = Hashtbl.find t.table (p, c) in
  Fixability.try_to_fix assign (Stack.top fixability_stack)


let gather_solution_from_cs t assign p cs ~change:cfix_state =
  List.fold_left
    (fun acc c ->
      (match try_to_fix t assign p c with
       |Some qformula ->
         let () = CFixState.fix cfix_state c in
         (c, qformula)::acc
       |None -> acc
      )
    )
    []
    cs

let propagate_c_fixed_info t graph assign cfix_state p new_fixed_cs
                           ~may_change:(pfixable_counter, pfix_state, queue) = 
  List.iter     
    (tell_related_predicate_constraint_is_fixed
       t graph assign cfix_state p 
       ~may_change:(pfixable_counter, pfix_state, queue))
    new_fixed_cs

let propagate_p_fixed_info t graph assign cfix_state p remain_unfix_cs
                           ~may_change:(pfixable_counter, pfix_state, queue) = 
  List.iter
    (tell_constraint_predicate_is_fixed
       t graph assign cfix_state p
       ~may_change:(pfixable_counter, pfix_state, queue))
    remain_unfix_cs

  
(*  pがfixしたことをcsに電波, csはunfix *)
let fix t graph assign p priority
        ~may_change:(cfix_state, pfixable_counter, pfix_state, queue) =
  let unfixed_pos_cs = List.filter (CFixState.isnt_fixed cfix_state) (G.pos_cs graph p) in
  let unfixed_neg_cs =  List.filter (CFixState.isnt_fixed cfix_state) (G.neg_cs graph p) in
  if priority.Priority.pol = Polarity.pos then
    let solution_asc = gather_solution_from_cs t assign p unfixed_pos_cs
                                               ~change:cfix_state
    in
    let new_fixed_cs = List.map fst solution_asc in
    let remain_unfix_cs = List.fold_left
                            (fun acc c ->
                              if CFixState.isnt_fixed cfix_state c then
                                c::acc
                              else
                                acc)
                            unfixed_neg_cs
                            unfixed_pos_cs
    in
    (* ここ、 *)
    let () = propagate_c_fixed_info
               t graph assign cfix_state p new_fixed_cs
               ~may_change:(pfixable_counter, pfix_state, queue)
           
    in
    let () = propagate_p_fixed_info
               t graph assign cfix_state p remain_unfix_cs
               ~may_change:(pfixable_counter, pfix_state, queue) 
    in
    solution_asc
  else
    let solution_asc = gather_solution_from_cs t assign p unfixed_neg_cs
                                               ~change:cfix_state
    in
    let new_fixed_cs = List.map fst solution_asc in
    let remain_unfix_cs = List.fold_left
                            (fun acc c ->
                              if CFixState.isnt_fixed cfix_state c then
                                c::acc
                              else
                                acc)
                            unfixed_pos_cs
                            unfixed_neg_cs
    in
    
    let () = propagate_c_fixed_info
               t graph assign cfix_state p new_fixed_cs
               ~may_change:(pfixable_counter, pfix_state, queue)
    in
    let () = propagate_p_fixed_info
               t graph assign cfix_state p remain_unfix_cs
               ~may_change:(pfixable_counter, pfix_state, queue)           
    in
    solution_asc        
    
    
    
    
    
module Constructor = struct

  let add_pc_fixiability t p c flexiability wait_pc =
    let stack = Stack.create () in
    let () = Stack.push flexiability stack  in
    let () = Hashtbl.add t.table (p,c) stack in
    let () = update_affect t p c wait_pc in
    ()

  (* 可能な（p - c）の組に空のaffectを追加する *)
  let add_empty_affect graph affect =
    G.iter_p
      (fun p ->
        List.iter
          (fun c ->
            Hashtbl.add affect (p,c) [])
          ((G.pos_cs graph p)@(G.neg_cs graph p))
      )
    graph
    
    

  let gen_t graph = 
    let fixability_map:(Fixability.t * S.t) M.t CMap.t =
      G.fold_c
        (fun c_lav acc ->
          let c = G.cons_of_cLavel graph c_lav in
          let m =  Fixability.Constructor.gen_fixability_map graph c in
          CMap.add c_lav m acc)
        graph
        CMap.empty
    in
    (* initialize *)
    let t = {table = Hashtbl.create (2*(G.cNode_num graph) * (G.pNode_num graph ));
             affect = Hashtbl.create ((G.cNode_num graph) * (G.pNode_num graph))}
    in
    let () = add_empty_affect graph t.affect in
    let () = CMap.iter
               (fun c (map:(Fixability.t * S.t) M.t) ->
                 M.iter
                   (fun p_id (fixability, wait_pc_id) ->
                     let wait_pc = PSet.of_id_Set graph wait_pc_id in
                     let p = G.pLavel_of_id graph p_id in
                     add_pc_fixiability t p c fixability wait_pc)
                   map )
               fixability_map
    in
    t

  let pos_count_fixable_unfixable t graph p =
    List.fold_left
      (fun (fixable, unfixable) c ->
        if is_fixable t p c then
          (fixable + 1, unfixable)
        else
          (fixable, unfixable + 1)
      )
      (0, 0)
      (G.pos_cs graph p)


  let neg_count_fixable_unfixable t graph p =
    List.fold_left
      (fun (fixable, unfixable) c ->
        if is_fixable t p c then
          (fixable + 1, unfixable)
        else
          (fixable, unfixable + 1)
      )
      (0, 0)
      (G.neg_cs graph p)
    

  (* この時点で、tの初期化は完了している *)
  let pos_registor graph t ~change:(fixable_count, pfix_state, queue) =
    G.iter_p
      (fun p ->
        let gen_pmap = (fun () -> count_other_unknown_in_cs t graph M.empty p
                                                            (G.pos_cs graph p)
                       )
        in
        let fixable, unfixable = pos_count_fixable_unfixable t graph p in
        PFixableConstraintCounter.Constructor.pos_registor fixable_count p fixable unfixable gen_pmap
                                                           ~change:(pfix_state, queue)
      )
      graph

  (* この時点で、tの初期化は完了している *)
  let neg_registor graph t ~change:(fixable_count, pfix_state, queue) =
    G.iter_p
      (fun p ->
        let gen_pmap = (fun () -> count_other_unknown_in_cs t graph M.empty p
                                                            (G.neg_cs graph p)
                       )
        in
        let fixable, unfixable = neg_count_fixable_unfixable t graph p in
        PFixableConstraintCounter.Constructor.neg_registor fixable_count p fixable unfixable gen_pmap
                                                           ~change:(pfix_state, queue)
      )
    graph    
        

  let f up_p_set graph =
    let t = gen_t graph in
    let p_num = G.pNode_num graph in
    (* 以下を初期化 *)
    let fixable_count = PFixableConstraintCounter.Constructor.create p_num in
    let pfix_state = PFixState.Constructor.create p_num in
    let queue = PriorityQueue.create up_p_set p_num in
    let () = pos_registor graph t ~change:(fixable_count, pfix_state, queue) in
    let () = neg_registor graph t ~change:(fixable_count, pfix_state, queue) in    
    (t, fixable_count, pfix_state, queue)
    
end
