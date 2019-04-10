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
               ;env:Liq.env
               ;pos: cLavel list
               ;neg: cLavel list
               }

  type t = {cTable: cNode array;
            pTable: pNode array;
            pIdHash: (Id.t, pLavel) Hashtbl.t
           }

  val pLavel_of_id: t -> Id.t -> pLavel
    
  val pos_p: t -> cLavel -> pLavel

  val neg_ps: t -> cLavel ->pLavel list
    
  val pos_cs: t -> pLavel -> cLavel list
    
  val neg_cs: t -> pLavel -> cLavel list

  val get_p_env: t -> pLavel -> Liq.env

    
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
               ;env: Liq.env
               ;pos: cLavel list
               ;neg: pLavel list
               }

  type t = {cTable: cNode array;
            pTable: pNode array
            ;pIdHash: (Id.t, pLavel) Hashtbl.t
           }

  let pLavel_of_id t id =
    try Hashtbl.find t.pIdHash id with
      Not_found -> invalid_arg "pLavel_of_id: invalid id"
         
  let pos_p graph c_lav =
    graph.cTable.(c_lav).pos

  let neg_ps graph c_lav =
    graph.cTable.(c_lav).neg

  let pos_cs graph p =
    graph.pTable.(p).pos

  let neg_cs graph p =
    graph.pTable.(p).neg

  let get_p_env graph p =
    graph.pTable.(p).env

end

module PMap =
  Map.Make
    (struct
      type t = G.pLavel
      let compare = compare
    end)

module PSet = struct
 include ( Set.Make
                (struct
                  type t = G.pLavel
                  let compare = compare
                end))
  (* include PS *)

  let of_id_Set graph id_set =
    S.fold
      (fun id acc ->
        add (G.pLavel_of_id graph id) acc)
    id_set
    empty
    
end

  

(* predicateだけからなるグラフ *)
(* \Gamma|- pが、
   \Gamma; p; q -> ... 
   の時　p -neg-> q
   
 *)
module PG = struct
  
  type t = {posTable: (G.pLavel list) array
           ;negTable: (G.pLavel list) array
           }

  let pos_ps t p = t.posTable.(G.int_of_pLavel p)

  let neg_ps t p = t.negTable.(G.int_of_pLavel p)                 
  
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
           ;otherPCount: int
           ;fixableNum:int
           ;pol: Polarity.t
           ;lavel: G.pLavel }
         
end

                
module PriorityQueue:
sig

  type t

  val pop: t -> (G.pLavel * Polarity.t * Priority.t) option

  val push_pos: t -> G.pLavel -> Priority.t -> unit

  val push_neg: t -> G.pLavel -> Priority.t -> unit    

  val update_pos: t -> G.pLavel -> Priority.t -> unit

  val update_neg: t -> G.pLavel -> Priority.t -> unit    
    
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

      
  type t = {posTable: Priority.t array
           ;negTable: Priority.t array
           ;table: Priority.t array
           ;internalQueue: InternalQueue.t
           }


  let rec pop ({table = table; internalQueue = internal_queue} as queue) =
    match InternalQueue.pop internal_queue with
    |None -> None
    |Some priority ->
      let p = priority.Priority.lavel in
      let priority' =  table.(G.int_of_pLavel p) in
      if priority = priority' then
        Some (p, priority.pol, priority)      (* table はpopされた時のものに保たれる *)
      else                        (* updated old element *)
        pop queue


  let push_pos {posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority = 
    pos_table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    if priority < neg_table.(G.int_of_pLavel p) then
      (table.(G.int_of_pLavel p) <- priority;
       InternalQueue.push internal_queue priority)
    else
      ()

  let push_neg {posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority = 
    neg_table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    if priority < pos_table.(G.int_of_pLavel p) then
      (table.(G.int_of_pLavel p) <- priority;
       InternalQueue.push internal_queue priority)
    else
      ()    

  let update_pos = push_pos

  let update_neg = push_neg
      
      
end

(* 怪しい *)
module PFixState = struct

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
        table.(G.int_of_pLavel p) <- PartialFixable
        else if fixable_level = PredicateFixableLevel.zero then
        table.(G.int_of_pLavel p) <- ZeroFixable
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
      (pos_update' t p fixable_level);
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
      (neg_update' t p fixable_level);
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
      
             
end
    


   
(* Fix information (dynamic) *)
module PFixableConstraintCounter:
sig
  
 type fixRatio = {fixable: int ref ; unfixable: int ref }


  type t 

         (* val decr_pos_unfix: t -> G.pLavel -> unit *)

         (* val decr_neg_unfix: t -> G.pLavel -> unit *)
     
  val unfixable2fixable: t -> G.pLavel -> Polarity.t -> (unit -> int PMap.t) ->
      may_change:(PFixState.t * PriorityQueue.t) -> unit
    
end= struct
  

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
           }               

  (* 要求:
     pはfixedではない、
     unficable > 0
     unfixableをfixableにする
   *)
  (* unfixable--; fixable++ *)
  let unfixable2fixable t p pol (calc_othere_p:unit -> int PMap.t)
                        ~may_change:(pfix_state, queue) =
    if pol = Polarity.pos then
      let fix_ratio = t.posRatio.(G.int_of_pLavel p) in
      let unfixable = fix_ratio.unfixable in
      let fixable = fix_ratio.fixable in
      (assert (!unfixable > 0));
      (decr unfixable);
      (incr fixable);
      if !unfixable = 0 then
        let map = calc_othere_p () in
        PFixState.pos_update2allfixable pfix_state p map
                                        !fixable ~change:queue
      else if !fixable = 1 then
        PFixState.pos_update pfix_state p (to_fixable_level fix_ratio)
                             ~change:queue
      else
        ()
    else
      let fix_ratio = t.negRatio.(G.int_of_pLavel p) in
      let unfixable = fix_ratio.unfixable in
      let fixable = fix_ratio.fixable in
      (assert (!unfixable > 0));      
      (decr unfixable);
      (incr fixable);
      if !unfixable = 0 then
        let map = calc_othere_p () in
        PFixState.neg_update2allfixable pfix_state p map
                                        !fixable ~change:queue
     else if !fixable = 1 then
        PFixState.neg_update pfix_state p (to_fixable_level fix_ratio)
                             ~change:queue
      else
        ()    


  (* fixable--; unfixalbe (unchange)  *)
  let remove_fixable t p pol (calc_othere_p:unit -> int PMap.t)
                     ~may_change:(pfix_state, queue) =
    if pol = Polarity.pos then
      let fix_ratio = t.posRatio.(G.int_of_pLavel p) in
      let unfixable = fix_ratio.unfixable in
      let fixable = fix_ratio.fixable in
      (assert (!fixable > 0));
      (decr fixable);
      if !unfixable = 0 then    (* allfixable -> allfixabl *)
        let map = calc_othere_p () in
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
        let map = calc_othere_p () in
        PFixState.neg_decr_othere_p_form_allfixable pfix_state p map ~change:queue
      else if !fixable = 0 then (* unfixable > 0: * -> zero fixable *)
        PFixState.neg_update pfix_state p PredicateFixableLevel.zero ~change:queue
      else  (* unfixable > 0 && fixable > 0: partial -> partial *)
        ()      


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

  let fix t p c  = 
    (t.isFix.(G.int_of_cLavel c) <- true)
    



end


module Fixability = struct

  (* constraint中の、pの位置を保持する:　   \gamma;p;\delata |- e1 -> e2 etc *)
  type pPosition =
    |Positive of {env: Liq.env
                 ;negFormula: Formula.t
                (*  p is here *)
                 }
    |Negative of {backEnv: Liq.env
                (*  p is here *)                 
                 ;frontEnv: Liq.env 
                 ;posFormula:Formula.t}

  type bound =
    (* env|- \phi -> p *)
    |LowBound of {localEnv: Liq.env
                 ;vars: S.t
                 ;require: Formula.t (* no unknown p in boud *)
                 }
    (* env|- p -> \phi *)
    (* env;p;delta'|- \phi1 -> \phi2 *)
    |UpBound of {localEnv: Liq.env
                ;vars: S.t
                ;require: (Liq.env * Formula.t) (* no unknown p in bound *)
                }

  let unknown_in_localEnv assign = function
    |LowBound {localEnv = local_env} |UpBound {localEnv = local_env} ->
      S.filter
        (fun x ->not (M.mem x assign))
        (Liq.env_extract_unknown_p local_env)

      

  let predicate_polarity_of_bound = function
    |LowBound _ -> Polarity.pos
    |UpBound _ -> Polarity.neg
                

  let extract_necessary_predicate senv unknown env =
    Liq.env_fold
      (fun (x,sch) (acc_unknown, acc_p) ->
        if  (S.mem x acc_unknown) then
          match sch with
          |([], [], Liq.TScalar (_, phi)) ->
            let phi_fv = (Formula.fv phi) in (* = fv ([_v->x].phi) / {x}  *)
            let new_unknown' = S.filter (fun x -> Formula.Senv.mem x senv) phi_fv  in
            let acc_unknown' = S.union new_unknown' acc_unknown in
            let acc_p' = S.union acc_p (Formula.extract_unknown_p phi) in
            (acc_unknown', acc_p')
          | _ -> (acc_unknown, acc_p)
        else
          (acc_unknown, acc_p)
      )    
      (fun phi (acc_unknown, acc_p) ->
        let phi_fv = (Formula.fv_include_v phi) in
        if S.is_empty (S.inter  phi_fv acc_unknown) then
          (acc_unknown, acc_p)
        else
          let new_unknown' = S.filter (fun x -> Formula.Senv.mem x senv) phi_fv  in
          let acc_unknown' = S.union new_unknown' acc_unknown in
          let acc_p' = S.union acc_p (Formula.extract_unknown_p phi) in
          (acc_unknown', acc_p')
      )
    env
    (unknown, S.empty)

  let rec iter_extract_necessary_predicate senv unknown env =
    let unknown', necess_p = extract_necessary_predicate senv unknown env in
    if unknown' = unknown then
      necess_p
    else
      iter_extract_necessary_predicate senv unknown' env
          
    
  let wait_predicates assign senv = function
    |LowBound {localEnv = local_env; vars = vars; require = _}
     |UpBound {localEnv = local_env; vars = vars; require = _ } ->
      let local_env' = Liq.env_substitute_F assign local_env in
      iter_extract_necessary_predicate senv vars local_env'

      

  let rec extract_subst senv acc_sita eq_list =
    let open Formula in
    match List.pop
            (function |(x, Var (_,y)) -> not (Senv.mem y senv)
                      | _ -> false)
            eq_list
    with
    |Some ((x, Var (sort, y)), eq_list') ->
      let y2x = M.singleton y (Var (sort, x)) in
      let eq_list' = List.map (fun (x,e) -> (x, substitution y2x e)) eq_list' in
      extract_subst senv (subst_compose y2x acc_sita) eq_list'
    |Some _ -> assert false     (* popの条件から *)
    |None -> acc_sita, eq_list

           
  let mk_fresing_subst senv sita =
    M.fold
      (fun x e acc ->
        let x_sort = try Formula.Senv.find x senv with _ -> assert false in
        let x' = Id.genid x in
        M.add x (Formula.Var (x_sort, x')) acc)
      M.empty
    sita
        
        
  let mk_flatten_subst senv sita =
    let freshing_sita = mk_fresing_subst senv sita in
    let eq_list = M.bindings (Formula.subst_compose freshing_sita sita) in
    let delta, eq_list' = extract_subst senv M.empty eq_list in
    let eq_phi = eq_list'
                 |> List.map
                      (fun (x,e) ->
                        let x_sort = try Formula.Senv.find x senv with _ -> assert false in
                        Formula.Eq (Formula.Var (x_sort, x), e))
                 |> Formula.and_list
    in
               
    (Formula.subst_compose delta freshing_sita), eq_phi
    
               
  let mk_bound assign senv env pending_sita = function
    |Positive {env = cons_env; negFormula = e1 } ->
      (match Liq.env_suffix cons_env env with
       |None -> invalid_arg "Solver.mk_bound: cons_env and env mismatch"
       |Some local_env ->
         let flatten_sita, eq_phi = mk_flatten_subst senv pending_sita in
         let local_env' = Liq.env_substitute_F assign local_env (* ここはやらなくても良い *)
                          |>Liq.env_substitute_F flatten_sita
         in
         let e1' = Formula.substitution assign e1 
                   |>Formula.substitution flatten_sita
         in
         let require = Formula.And (e1', eq_phi) in
         let vars = S.filter (fun x -> not (Formula.Senv.mem x senv))
                             (Formula.fv require)
         in
         LowBound {localEnv = local_env'
                  ;vars = vars
                  ;require = require}
      )
    |Negative {backEnv = cons_back_env
              ;frontEnv = cons_front_env
              ;posFormula = e1} ->
      (match Liq.env_suffix cons_back_env env with
       |None -> invalid_arg "Solver.mk_bound: cons_env and env mismatch"
       |Some local_env ->
         let flatten_sita, eq_phi = mk_flatten_subst senv pending_sita in
         let local_env' = Liq.env_substitute_F assign local_env (* ここはやらなくても良い *)
                          |>Liq.env_substitute_F flatten_sita
         in
         let e1' = Formula.substitution assign e1 
                   |>Formula.substitution flatten_sita
         in
         let cons_front_env' = Liq.env_substitute_F assign cons_front_env
                               |>Liq.env_substitute_F flatten_sita
         in
         let require_env = Liq.env_add_F cons_front_env' eq_phi in
         let require = (require_env, e1') in
         let require_fv = Liq.env2formula_all require_env
                        |> Formula.fv_include_v
                        |>S.union (Formula.fv_include_v e1')
         in
         let vars = S.filter (fun x -> not (Formula.Senv.mem x senv))
                             require_fv
         in
         UpBound {localEnv = local_env'
                 ;vars = vars
                 ;require = require})
       (* ここで、env2formulaして、fvをとる、下のqformula_of_boundでも同じようにやる
        しかし、envを持つ理由が汚い気がする*)
         
         
         

  let qformula_of_bound assign = function
    |UpBound {localEnv = env; vars = vars; require = (delta, phi) } ->  (* env|- p -> \phi *)
      let env_phi = Liq.env_substitute_F assign env
                             |> Liq.env2formula_all
                             |> Formula.list_and
                             |> List.filter (function |Formula.Unknown _ -> false
                                                      | _ -> true
                                            )
      in
      let delta_phi = Liq.env2formula_all delta (* delat contain no unknown p *)
                      |> Formula.list_and
      in
      let qformula_premise = delta_phi@env_phi in
      let qformula_fv =
        List.fold_left
          (fun acc phi -> S.union acc (Formula.fv_include_v phi))
          S.empty
          (phi::qformula_premise)
      in
      let local_senv = Liq.mk_sort_env (Liq.env_append env delta) in
      (* (assert (S.for_all *)
      (*            (fun x -> Formula.Senv.mem x senv ||Formula.Senv.mem x local_senv ) *)
      (*            qformula_fv)); *)
      let binding = List.filter
                      (fun (x,sort) -> S.mem x qformula_fv)
                      (Formula.Senv.reveal local_senv)
      in
      Formula.QAll (binding, qformula_premise, phi)

    |LowBound {localEnv = env; vars = vars; require = phi } ->  (* env|- p -> \phi *)
      let env_phi = Liq.env_substitute_F assign env
                             |> Liq.env2formula_all
                             |> Formula.list_and
                             |> List.filter (function |Formula.Unknown _ -> false
                                                      | _ -> true
                                            )
      in
      let qformula_fv =
        List.fold_left
          (fun acc phi -> S.union acc (Formula.fv_include_v phi))
          S.empty
          (phi::env_phi)
      in
      let local_senv = Liq.mk_sort_env env in
      (* (assert (S.for_all *)
      (*            (fun x -> Formula.Senv.mem x senv ||Formula.Senv.mem x local_senv ) *)
      (*            qformula_fv)); *)
      let binding = List.filter
                      (fun (x,sort) -> S.mem x qformula_fv)
                      (Formula.Senv.reveal local_senv)
      in
      Formula.QExist (binding, phi::env_phi)

      
      
  type t = |UnBound of {waitNum: int ref
                       ;senv:Formula.Senv.t
                       ;pendingSubst: Formula.subst
                       ;pendingSortSubst: Formula.sort_subst
                       ;position: pPosition
                       }
           |Bound of {waitNum: int ref (* waitNum >= 1 *)
                     ;firstWaitNum: int
                     ;senv:Formula.Senv.t
                     ;pendingSortSubst: Formula.sort_subst
                     ;bound: bound}
           |Fixable of (Polarity.t * bound)


  let count_othere_p t graph assign =
    match t with
    |Bound rc ->
      S.fold
        (fun p acc ->
          PMap.add (G.pLavel_of_id graph p) 1 acc) (* とりあえずここは今の所不正確 *)
        (unknown_in_localEnv assign rc.bound)
        PMap.empty
    | _ -> invalid_arg "count_othere_p: not bounded"
         
                     
  let upgrade_unbound assign p_env = function
    |UnBound {waitNum = n
             ;senv = senv
             ;pendingSubst = sita
             ;pendingSortSubst = sort_sita
             ;position = position } when !n = 0 ->
      let bound = mk_bound assign senv p_env sita position in
      let wait_ps = wait_predicates assign senv bound in
      let wait_num = S.cardinal wait_ps in
      if wait_num = 0 then
        let pol = predicate_polarity_of_bound bound in
        (Fixable (pol, bound), wait_ps)
      else
        (Bound {waitNum = ref wait_num
              ;firstWaitNum = wait_num
              ;senv = senv
              ;pendingSortSubst = sort_sita
              ;bound = bound}
        , wait_ps)
      
      
    |UnBound _ -> invalid_arg "unbound_to_bound: not yet bounded"
    |Bound _ |Fixable _ -> invalid_arg "unbound_to_bound: already bounded"
      
                     
                   
  let try_to_fix assign = function
    |Fixable (pol,bound) ->
      Some (qformula_of_bound assign bound)
    |_ ->
      None

  (* unboudのwaitnumをdecrementする。0になったらwait predicateを再計算し、新たなboundをreturnする *)
  let decr_wait_num assign graph p c ~change:fixability =
    match fixability with
    |Fixable _ -> invalid_arg "Fixability.decr_wait_num: can not decrement"
    |Bound rc ->
      let wait_num = rc.waitNum in
      let () = decr wait_num in
      if !wait_num = 0 then
        let new_wait_pc = wait_predicates assign rc.senv rc.bound
                          |> PSet.of_id_Set graph
        in
        let new_wait_num = PSet.cardinal new_wait_pc in
        if new_wait_num = 0 then
          let pol = predicate_polarity_of_bound rc.bound in
          Some (Fixable (pol, rc.bound), PSet.empty)
        else
          Some (Bound {waitNum = ref new_wait_num
                      ;firstWaitNum = new_wait_num
                      ;senv = rc.senv
                      ;pendingSortSubst = rc.pendingSortSubst
                      ;bound = rc.bound}
               ,new_wait_pc)
               
      else
        None
    |UnBound rc as unbound->
      let wait_num = rc.waitNum in
      let () = decr wait_num in
      if !wait_num = 0 then
        let new_bound, wait_pc  =
          upgrade_unbound assign (G.get_p_env graph p) unbound
        in
        Some (new_bound, (PSet.of_id_Set graph wait_pc))
      else
        None

  let is_fixable = function
    |Fixable _ -> true
    | _ -> false
  
end


module FixabilityManager = struct
  
  exception Cons_pred_mismatch of string
          
  type t = {table: ((G.pLavel * G.cLavel), Fixability.t Stack.t) Hashtbl.t
           ;affect: ((G.pLavel * G.cLavel), G.pLavel list) Hashtbl.t }

  let is_fixable t p c =
    let stack = Hashtbl.find t.table (p,c) in
    Fixability.is_fixable (Stack.top stack )

  (* (p,c) ->q,q',...
     pがfixした時に,constraint cでpを待っているpredicate
   *)

  let count_other_unknown_from_cs t graph assign cfix_state p cs = 
      List.fold_left
        (fun acc_map c ->
          if CFixState.is_fixed cfix_state c then
            acc_map
          else
            let fixability = Stack.top (Hashtbl.find t.table (p, c)) in
            let pmap = Fixability.count_othere_p fixability graph assign in
            PMap.union (fun q i i' -> Some (i+i')) pmap acc_map)
        PMap.empty
        cs

    
  let count_other_unknown t graph assign cfix_state pol p =
    if pol = Polarity.pos then
      count_other_unknown_from_cs t graph assign cfix_state p (G.pos_cs graph p)
    else
      count_other_unknown_from_cs t graph assign cfix_state p (G.neg_cs graph p)
    
    
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
         let calc = (fun () -> count_other_unknown t graph assign cfix_state pol q) in
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
      let pmap = count_other_unknown t assign graph cfix_state pol q in
      PFixableConstraintCounter.remove_fixable pfixable_counter q pol
                                               ~may_change:(pfix_state, queue)
    else
      PFixableConstraintCounter.remove_unfixable pfixable_counter q pol
                                                 ~may_change:(pfix_state, queue)


  let tell_related_predicate_constraint_is_fixed t graph p c
                                                 ~may_change:(pfixable_counter, pfix_state, queue) =
    let c_pos_p = (G.pos_p graph c) in
    let () =
      if PFixState.isnt_fixed pfix_state c_pos_p then
        tell_predicate_constraint_is_fixed t c c_pos_p
                                           ~may_change:(pfixable_counter, pfix_state, queue)
      else ()
    in
    let unfixed_neg_p = (List.filter (PFixState.isnt_fixed pfix_state) (G.neg_ps graph c)) in
  List.iter
    (fun q -> tell_predicate_constraint_is_fixed t c q
                                                 ~may_change:(pfixable_counter, pfix_state, queue))
    unfixed_neg_p
            
            
  
          
    

  let try_to_fix t assign p c =
    let fixability_stack = Hashtbl.find t.table (p, c) in
    Fixability.try_to_fix assign (Stack.top fixability_stack)
         
    (*  pがfixしたことをcsに電波, csはunfix *)
    let fix t graph assign p priority
            ~may_change:(cfix_state, pfix_state, pfixable_counter, queue) =
      if priority.Priority.pol = Polarity.pos then
        let unfixed_cs = List.filter (CFixState.is_fixed cfix_state) (G.pos_cs graph p) in
        List.fold_left
          (fun acc c ->
            (match try_to_fix t assign p c with
             |Some qformula ->
               let () = CFixState.fix cfix_state p c graph
                                      ~may_change:(pfixable_counter, queue)
                 in
                 (c, qformula)::acc
               |None ->         (* (p,c) unfixable  *)
                 (* tell predicate... *)
                
              
          []
          (G.pos_cs graph p)
  
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
