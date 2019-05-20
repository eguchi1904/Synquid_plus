module Liq = Type
module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
            
module Polarity = PredicatePriorityQueue.Polarity
module PredicateFixableLevel = PredicatePriorityQueue.PredicateFixableLevel
module PriorityQueue = PredicatePriorityQueue.PriorityQueue
module Priority = PredicatePriorityQueue.Priority

module PFixState = PredicateFixState

                 
type fixRatio = {fixable: int ref ; unfixable: int ref } 

              
let to_fixable_level  {fixable = fixable; unfixable =unfixable} =
  if !unfixable = 0 then      (* unfixable *)
    PredicateFixableLevel.all
  else if !fixable >  0 then
    PredicateFixableLevel.partial 
  else
    PredicateFixableLevel.zero
  

  
type t = {posRatio: fixRatio array
         ;negRatio: fixRatio array
         ;outerRatio: fixRatio option array
         }

let of_string graph t =
  let ratio_array2str arr =
    let _,str = Array.fold_left
                  (fun (i,acc_str) {fixable = fixable; unfixable =unfixable} ->
                    let p_id = G.id_of_int graph i in
                    let str = Printf.sprintf "%s -> {fixable = %d; unfixable = %d}\n" p_id !fixable !unfixable in
                    (i+1,acc_str^str))
                  (0,"")
                  arr
    in
    str
  in
  let out_ratio_array2str arr =
    let _,str = Array.fold_left
                  (fun (i,acc_str)  fix_ratio_opt ->
                    match fix_ratio_opt with
                    |Some {fixable = fixable; unfixable =unfixable} ->
                      let p_id = G.id_of_int graph i in
                      let str = Printf.sprintf "%s -> {fixable = %d; unfixable = %d}\n" p_id !fixable !unfixable in
                      (i+1,acc_str^str)
                    |None ->
                      let p_id = G.id_of_int graph i in
                      let str = Printf.sprintf "%s ->None" p_id in
                      (i+1,acc_str^str) 
                  )
                  (0,"")
                  arr
    in
    str
  in
  Printf.sprintf
    "Pos ratio\n--------------------------------------------------\n%s\nNeg ratio\n--------------------------------------------------\n%s\nOut Ratio\n--------------------------------------------------\n%s"
    (ratio_array2str t.posRatio)
    (ratio_array2str t.negRatio)
    (out_ratio_array2str t.outerRatio)
  

let unfixable2fixable_fixratio ~change:{ fixable = fixable_ref; unfixable = unfixable_ref } =
    (assert (!unfixable_ref > 0));
    (decr unfixable_ref);
    (incr fixable_ref);
    let fixable_level_change =(!fixable_ref = 1) || (!unfixable_ref = 0) in
    fixable_level_change

(* 要求:
     pはfixedではない、
     unficable > 0
     unfixableをfixableにする
 *)
(* unfixable--; fixable++ *)
let unfixable2fixable t graph p c pol (calc_othere_p:unit -> int PMap.t) (calc_othere_outer_opt:(unit -> int PMap.t) option )
                      ~may_change:(pfix_state, queue) =
  let is_outer = G.is_outer graph p c in
  if is_outer then
    begin
      match t.outerRatio.(G.int_of_pLavel p), calc_othere_outer_opt with
      |None, _ |_ , None -> assert false
      |Some fix_ratio_outer, Some calc_othere_outer ->
        let change_outer = unfixable2fixable_fixratio ~change:fix_ratio_outer in       
        if pol = Polarity.pos then
          let fix_ratio_pos = t.posRatio.(G.int_of_pLavel p) in
          let change = unfixable2fixable_fixratio ~change:fix_ratio_pos in    
          if change || change_outer then
            let new_fix_level = to_fixable_level fix_ratio_pos in
            let new_fix_level_outer = to_fixable_level fix_ratio_outer in
            PFixState.pos_update pfix_state graph p
                                 ~pos_info:(new_fix_level, calc_othere_p, !(fix_ratio_pos.fixable))
                                 ~outer_info:(Some (new_fix_level_outer, calc_othere_outer, !(fix_ratio_outer.fixable)))
                                 ~change:queue
          else
            ()
        else if pol = Polarity.neg then
          let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
          let change = unfixable2fixable_fixratio ~change:fix_ratio_neg in         
          if change || change_outer then
            let new_fix_level = to_fixable_level fix_ratio_neg in
            let new_fix_level_outer = to_fixable_level fix_ratio_outer in
            PFixState.neg_update pfix_state graph p
                                 ~neg_info:(new_fix_level, calc_othere_p, !(fix_ratio_neg.fixable))
                                 ~outer_info:(Some (new_fix_level_outer, calc_othere_outer, !(fix_ratio_outer.fixable)))
                                 ~change:queue
          else
            ()
        else
          assert false
    end           
  else                          (* not outer *)
    if pol = Polarity.pos then
      let fix_ratio_pos = t.posRatio.(G.int_of_pLavel p) in
      let change = unfixable2fixable_fixratio ~change:fix_ratio_pos in          
      if change then
        let new_fix_level = to_fixable_level fix_ratio_pos in
        PFixState.pos_update pfix_state graph p
                             ~pos_info:(new_fix_level, calc_othere_p, !(fix_ratio_pos.fixable))
                             ~outer_info:None
                             ~change:queue        
      else
        ()
    else if pol = Polarity.neg then
      let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
      let change = unfixable2fixable_fixratio ~change:fix_ratio_neg in
      if change then
        let new_fix_level = to_fixable_level fix_ratio_neg in
        PFixState.neg_update pfix_state graph p
                             ~neg_info:(new_fix_level, calc_othere_p, !(fix_ratio_neg.fixable))
                             ~outer_info:None
                             ~change:queue
      else
        ()
    else
      assert false
     
let remove_fixable_fixratio ~change:{ fixable = fixable_ref; unfixable = unfixable_ref } =
    (assert (!fixable_ref > 0));
    (decr fixable_ref);
    let is_all2all = !unfixable_ref = 0 in
    let is_partial2zero = !unfixable_ref > 0 && !fixable_ref = 0 in
    is_all2all||is_partial2zero

(* calc_ohtereが呼ばれるのは、all2allの変化の時のみなのでassert failしない
 *)
let gen_calc_othere_pos pfix_state p calc_removing_othere_p = 
  fun () ->
    let rm_map = calc_removing_othere_p () in
    let othere_p_map =
      match PFixState.othere_pmap_of_allfixable_pos pfix_state p with
      |Some s -> s
      |None -> assert false
    in
    PMap.union
      (fun x i1 i2 -> Some (i1 - i2))
      othere_p_map
      rm_map
  
let gen_calc_othere_neg pfix_state p calc_removing_othere_p = 
  fun () ->
    let rm_map = calc_removing_othere_p () in
    let othere_p_map =
      match PFixState.othere_pmap_of_allfixable_neg pfix_state p with
      |Some s -> s
      |None -> assert false
    in
    PMap.union
      (fun x i1 i2 -> Some (i1 - i2))
      othere_p_map
      rm_map
  
let gen_calc_othere_outer pfix_state p calc_removing_othere_p = 
  fun () ->
    let rm_map = calc_removing_othere_p () in
    let othere_p_map =
      match PFixState.othere_pmap_of_allfixable_outer pfix_state p with
      |Some s -> s
      |None -> assert false
    in
    PMap.union
      (fun x i1 i2 -> Some (i1 - i2))
      othere_p_map
      rm_map
  
    

(* fixable--; unfixalbe (unchange)  *)
let remove_fixable t graph p c pol (calc_removing_othere_p:unit -> int PMap.t) (* outerは、同じなるのでいらない *)
                   ~may_change:(pfix_state, queue) =
  let is_outer = G.is_outer graph p c in
  if is_outer then
    begin
      match t.outerRatio.(G.int_of_pLavel p) with
      |None -> assert false
      |Some fix_ratio_outer ->
        let change_outer = remove_fixable_fixratio fix_ratio_outer in
        if pol = Polarity.pos then
          let fix_ratio_pos = t.posRatio.(G.int_of_pLavel p) in
          let change = remove_fixable_fixratio fix_ratio_pos in
          if change || change_outer then
            let fix_level' = to_fixable_level fix_ratio_pos in
            let fix_level_out' = to_fixable_level fix_ratio_outer in            
            let calc_other' = gen_calc_othere_pos pfix_state p calc_removing_othere_p in
            let calc_other_out' = gen_calc_othere_outer pfix_state p calc_removing_othere_p in
            PFixState.pos_update pfix_state graph p
                                 ~pos_info:(fix_level', calc_other', !(fix_ratio_pos.fixable))
                                 ~outer_info:(Some (fix_level_out', calc_other_out', !(fix_ratio_outer.fixable)))
                                 ~change:queue            
          else  (* unfixable > 0 && fixable > 0: partial -> partial *)
            ()
        else if pol = Polarity.neg then
          let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
          let change = remove_fixable_fixratio fix_ratio_neg in
          if change || change_outer then
            let fix_level' = to_fixable_level fix_ratio_neg in
            let fix_level_out' = to_fixable_level fix_ratio_outer in            
            let calc_other' = gen_calc_othere_neg pfix_state p calc_removing_othere_p in
            let calc_other_out' = gen_calc_othere_outer pfix_state p calc_removing_othere_p in
            PFixState.neg_update pfix_state graph p
                                 ~neg_info:(fix_level', calc_other', !(fix_ratio_neg.fixable))
                                 ~outer_info:(Some (fix_level_out', calc_other_out', !(fix_ratio_outer.fixable)))
                                 ~change:queue            
          else  (* unfixable > 0 && fixable > 0: partial -> partial *)
            ()          
    end
  else
    if pol = Polarity.pos then
      let fix_ratio_pos = t.posRatio.(G.int_of_pLavel p) in
      let change = remove_fixable_fixratio ~change:fix_ratio_pos in 
      if change then
        let new_fix_level = to_fixable_level fix_ratio_pos in
        let calc_othere' = gen_calc_othere_pos pfix_state p calc_removing_othere_p in
        PFixState.pos_update pfix_state graph p
                             ~pos_info:(new_fix_level, calc_othere', !(fix_ratio_pos.fixable))
                             ~outer_info:None
                             ~change:queue        
      else
        ()
    else if pol = Polarity.neg then
      let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
      let change = remove_fixable_fixratio ~change:fix_ratio_neg in 
      if change then
        let new_fix_level = to_fixable_level fix_ratio_neg in
        let calc_othere' = gen_calc_othere_neg pfix_state p calc_removing_othere_p in
        PFixState.pos_update pfix_state graph p
                             ~pos_info:(new_fix_level, calc_othere', !(fix_ratio_neg.fixable))
                             ~outer_info:None
                             ~change:queue        
      else
        ()      
    else
      assert false    

let remove_unfixable_fixratio ~change:{fixable = fixable_ref; unfixable = unfixable_ref } =
    (assert (!unfixable_ref > 0));
    (decr unfixable_ref);
    let to_all = !unfixable_ref = 0 in
    to_all
    
(* unfixable-- *)
(* 
remove_fixable
remove_unfixable
unfixable2fixable
これは同じパターンばかりで抽象化できる。 *)
let remove_unfixable t graph p c pol (calc_othere_p:unit -> int PMap.t) (calc_othere_outer_opt:(unit -> int PMap.t) option )
                     ~may_change:(pfix_state, queue) =
  let is_outer = G.is_outer graph p c in
  if is_outer then
    begin
      match t.outerRatio.(G.int_of_pLavel p), calc_othere_outer_opt with
      |None, _ |_ , None -> assert false
      |Some fix_ratio_outer, Some calc_othere_outer ->
        let change_outer = remove_unfixable_fixratio ~change:fix_ratio_outer in       
        if pol = Polarity.pos then
          let fix_ratio_pos = t.posRatio.(G.int_of_pLavel p) in
          let change = remove_unfixable_fixratio ~change:fix_ratio_pos in    
          if change || change_outer then
            let new_fix_level = to_fixable_level fix_ratio_pos in
            let new_fix_level_outer = to_fixable_level fix_ratio_outer in
            PFixState.pos_update pfix_state graph p
                                 ~pos_info:(new_fix_level, calc_othere_p, !(fix_ratio_pos.fixable))
                                 ~outer_info:(Some (new_fix_level_outer, calc_othere_outer, !(fix_ratio_outer.fixable)))
                                 ~change:queue
          else
            ()
        else if pol = Polarity.neg then
          let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
          let change = remove_unfixable_fixratio ~change:fix_ratio_neg in         
          if change || change_outer then
            let new_fix_level = to_fixable_level fix_ratio_neg in
            let new_fix_level_outer = to_fixable_level fix_ratio_outer in
            PFixState.neg_update pfix_state graph p
                                 ~neg_info:(new_fix_level, calc_othere_p, !(fix_ratio_neg.fixable))
                                 ~outer_info:(Some (new_fix_level_outer, calc_othere_outer, !(fix_ratio_outer.fixable)))
                                 ~change:queue
          else
            ()
        else
          assert false
    end           
  else                          (* not outer *)
    if pol = Polarity.pos then
      let fix_ratio_pos = t.posRatio.(G.int_of_pLavel p) in
      let change = remove_unfixable_fixratio ~change:fix_ratio_pos in          
      if change then
        let new_fix_level = to_fixable_level fix_ratio_pos in
        PFixState.pos_update pfix_state graph p
                             ~pos_info:(new_fix_level, calc_othere_p, !(fix_ratio_pos.fixable))
                             ~outer_info:None
                             ~change:queue        
      else
        ()
    else if pol = Polarity.neg then
      let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
      let change = remove_unfixable_fixratio ~change:fix_ratio_neg in
      if change then
        let new_fix_level = to_fixable_level fix_ratio_neg in
        PFixState.neg_update pfix_state graph p
                             ~neg_info:(new_fix_level, calc_othere_p, !(fix_ratio_neg.fixable))
                             ~outer_info:None
                             ~change:queue
      else
        ()
    else
      assert false


module Constructor = struct

  let dummy_ratio = {fixable = ref (-1) ; unfixable = ref (-1) } 

  let create size = {posRatio = Array.make size dummy_ratio;
                     negRatio = Array.make size dummy_ratio;
                     outerRatio = Array.make size None}

  (* tと、pfix_stateのouterの値を初期化する *)
  let outer_registor t p outer_info_opt ~change:pfix_state =
    match outer_info_opt with
    |Some (fixable_c, unfixable_c, calc_othere_out) ->
      let fix_ratio = {fixable = ref fixable_c; unfixable = ref unfixable_c } in
      let () = t.outerRatio.(G.int_of_pLavel p) <- Some fix_ratio in
      let fix_level = to_fixable_level fix_ratio in
      PFixState.Constructor.outer_register pfix_state p fix_level fixable_c calc_othere_out
    |None ->
      let () = t.outerRatio.(G.int_of_pLavel p) <- None in
      ()

  (* outer_registerを読んだ後に呼び出す *)
  let pos_registor t graph p fixable_c unfixable_c calc_other calc_other_out_opt
                   ~change:(pfix_state, queue) = 
    let fix_ratio_pos = {fixable = ref fixable_c; unfixable = ref unfixable_c } in
    let () = t.posRatio.(G.int_of_pLavel p) <- fix_ratio_pos in
    (* pfix_stateへの反映 *)
    let fix_level_pos = to_fixable_level fix_ratio_pos in    
    match t.outerRatio.(G.int_of_pLavel p), calc_other_out_opt with
    |Some fix_ratio_out, Some calc_other_out ->
      let fix_level_out = to_fixable_level fix_ratio_out in
      PFixState.pos_update
        pfix_state graph p
        ~pos_info:(fix_level_pos, calc_other, fixable_c)
        ~outer_info:(Some (fix_level_out, calc_other_out, !(fix_ratio_out.fixable)))
        ~change:queue
    |None, None ->
      PFixState.pos_update
        pfix_state graph p
        ~pos_info:(fix_level_pos, calc_other, fixable_c)
        ~outer_info:None
        ~change:queue
    |_ -> assert false

      
  (* outer_registerを読んだ後に呼び出す *)
  let neg_registor t graph p fixable_c unfixable_c calc_other calc_other_out_opt
                   ~change:(pfix_state, queue) = 
    let fix_ratio_neg = {fixable = ref fixable_c; unfixable = ref unfixable_c } in
    let () = t.negRatio.(G.int_of_pLavel p) <- fix_ratio_neg in
    (* pfix_stateへの反映 *)
    let fix_level_neg = to_fixable_level fix_ratio_neg in    
    match t.outerRatio.(G.int_of_pLavel p), calc_other_out_opt with
    |Some fix_ratio_out, Some calc_other_out ->
      let fix_level_out = to_fixable_level fix_ratio_out in
      PFixState.neg_update
        pfix_state graph p
        ~neg_info:(fix_level_neg, calc_other, fixable_c)
        ~outer_info:(Some (fix_level_out, calc_other_out, !(fix_ratio_out.fixable)))
        ~change:queue
    |None, None ->
      PFixState.neg_update
        pfix_state graph p
        ~neg_info:(fix_level_neg, calc_other, fixable_c)
        ~outer_info:None
        ~change:queue
    |_ -> assert false

end
