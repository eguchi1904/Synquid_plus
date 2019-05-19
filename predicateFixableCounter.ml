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
  Printf.sprintf
    "Pos ratio\n--------------------------------------------------\n%s\nNeg ratio\n--------------------------------------------------\n%s"
    (ratio_array2str t.posRatio)
    (ratio_array2str t.negRatio)
  

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
let unfixable2fixable t graph c p pol (calc_othere_p:unit -> int PMap.t) (calc_othere_outer_opt:(unit -> int PMap.t) option )
                      ~may_change:(pfix_state, queue) =
  let is_outer = G.is_outer graph c p in
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
            PFixState.pos_update pfix_state p
                                 ~pos_info:(new_fix_level, calc_othere_p, !(fix_ratio_pos.fixable))
                                 ~outer_info:(Some (new_fix_level_outer, calc_othere_p_outer, !(fix_ratio_outer.fixable)))
                                 ~change:queue
          else
            ()
        else if pol = Polarity.neg then
          let fix_ratio_neg = t.negRatio.(G.int_of_pLavel p) in
          let change = unfixable2fixable_fixratio ~change:fix_ratio_neg in         
          if change || change_outer then
            let new_fix_level = to_fixable_level fix_ratio_neg in
            let new_fix_level_outer = to_fixable_level fix_ratio_outer in
            PFixState.neg_update pfix_state p
                                 ~neg_info:(new_fix_level, calc_othere_p, !(fix_ratio_neg.fixable))
                                 ~outer_info:(Some (new_fix_level_outer, calc_othere_p_outer, !(fix_ratio_outer.fixable)))
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
        PFixState.pos_update pfix_state p
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
        PFixState.neg_update pfix_state p
                             ~neg_info:(new_fix_level, calc_othere_p, !(fix_ratio_pos.fixable))
                             ~outer_info:None
                             ~change:queue
      else
        ()
    else
      assert false
     
        

(* fixable--; unfixalbe (unchange)  *)
let remove_fixable t p pol (calc_removing_othere_p:unit -> int PMap.t)
                   ~may_change:(pfix_state, queue) =
  if pol = Polarity.pos then
    let fix_ratio = t.posRatio.(G.int_of_pLavel p) in
    let unfixable = fix_ratio.unfixable in
    let fixable = fix_ratio.fixable in
    (assert (!fixable > 0));
    (decr fixable);
    if !unfixable = 0 then    (* allfixable -> allfixabl *)
      let map = calc_removing_othere_p () in
      PFixState.pos_decr_othere_p_form_allfixable pfix_state p map ~change:queue
    else if !fixable = 0 then (* unfixable > 0: * -> zero fixable *)
      PFixState.pos_update pfix_state p PredicateFixableLevel.zero ~change:queue
    else  (* unfixable > 0 && fixable > 0: partial -> partial *)
      ()
  else
    let fix_ratio = t.negRatio.(G.int_of_pLavel p) in
    let unfixable = fix_ratio.unfixable in
    let fixable = fix_ratio.fixable in
    (assert (!fixable > 0));
    (decr fixable);
    if !unfixable = 0 then    (* allfixable -> allfixabl *)
      let map = calc_removing_othere_p () in
      PFixState.neg_decr_othere_p_form_allfixable pfix_state p map ~change:queue
    else if !fixable = 0 then (* unfixable > 0: * -> zero fixable *)
      PFixState.neg_update pfix_state p PredicateFixableLevel.zero ~change:queue
    else  (* unfixable > 0 && fixable > 0: partial -> partial *)
      ()

    
(* unfixable-- *)
let remove_unfixable t p pol (calc_othere_p:unit -> int PMap.t)
                     ~may_change:(pfix_state, queue) =
  if pol = Polarity.pos then
    let fix_ratio = t.posRatio.(G.int_of_pLavel p) in
    let unfixable = fix_ratio.unfixable in
    let fixable = fix_ratio.fixable in
    (assert (!unfixable > 0));
    (decr unfixable);
    if !unfixable = 0 then    (* (partial| zero) -> allfixable *)
      let map = calc_othere_p () in
      PFixState.pos_update2allfixable pfix_state p map !fixable ~change:queue
    else                      (* partial -> partila or zero -> zero  *)
      ()
  else
    let fix_ratio = t.negRatio.(G.int_of_pLavel p) in
    let unfixable = fix_ratio.unfixable in
    let fixable = fix_ratio.fixable in
    (assert (!unfixable > 0));
    (decr unfixable);
    if !unfixable = 0 then    (* (partial| zero) -> allfixable *)
      let map = calc_othere_p () in
      PFixState.neg_update2allfixable pfix_state p map !fixable ~change:queue
    else                      (* partial -> partila or zero -> zero  *)
      ()      
    

module Constructor = struct

  let dummy_ratio = {fixable = ref (-1) ; unfixable = ref (-1) } 

  let create size = {posRatio = Array.make size dummy_ratio;
                     negRatio = Array.make size dummy_ratio }


  let pos_registor t p fixable_c unfixable_c (calc_other:unit -> int PMap.t)
                   ~change:(pfix_state, queue) = 
    let fix_ratio = {fixable = ref fixable_c; unfixable = ref unfixable_c } in
    let () = t.posRatio.(G.int_of_pLavel p) <- fix_ratio in
    (* pfix_stateへの反映 *) 
    let fixable_lev = to_fixable_level fix_ratio in
    if fixable_lev  = PredicateFixableLevel.all then
      let map = calc_other () in
      PFixState.Constructor.pos_registor_allfixable pfix_state p map fixable_c ~change:queue
    else
      PFixState.Constructor.pos_registor pfix_state p fixable_lev ~change:queue


  let neg_registor t p fixable_c unfixable_c (calc_other:unit -> int PMap.t)
                   ~change:(pfix_state, queue) = 
    let fix_ratio = {fixable = ref fixable_c; unfixable = ref unfixable_c } in
    let () = t.negRatio.(G.int_of_pLavel p) <- fix_ratio in
    (* pfix_stateへの反映 *)
    let fixable_lev = to_fixable_level fix_ratio in
    if fixable_lev  = PredicateFixableLevel.all then
      let map = calc_other () in
      PFixState.Constructor.neg_registor_allfixable pfix_state p map fixable_c ~change:queue
    else

      PFixState.Constructor.neg_registor pfix_state p fixable_lev ~change:queue
    
end
