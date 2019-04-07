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
               ;neg: cLavel list
               }

  type t = {cTable: cNode array; pTable: pNode array }

  val pos_p: t -> cLavel -> pLavel

  val neg_ps: t -> cLavel ->pLavel list
    
  val pos_cs: t -> pLavel -> cLavel list
    
  val neg_cs: t -> pLavel -> cLavel list    

    
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

  let pos_cs graph p =
    graph.pTable.(p).pos

  let neg_cs graph p =
    graph.pTable.(p).neg

end

module PMap =
  Map.Make
    (struct
      type t = G.pLavel
      let compare = compare
    end)    
  

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
        Some (p, priority)      (* table はpopされた時のものに保たれる *)
      else                        (* updated old element *)
        pop queue


  let push {table = table; internalQueue = internal_queue} p priority = 
    table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    InternalQueue.push internal_queue priority

  let update = push
      
      
end

(* 怪しい *)
module PFixState = struct

  type state = |Fixed of state  (* pre state *)
               |AllFixable of (int * int PMap.t)
               |PartialFixable 
               |ZeroFixable

               
               
  type t = {posTable: state array
           ;negTable: state array
           
           ;posAffect: int PMap.t array
           ;negAffect: int PMap.t array

           }           


  (* この時点で、pをfixしたことによる、fixableLevelの変化は反映されていないといけない *)
    let fix {posTable = pos_table
            ;negTable =  neg_table
            ;posAffect =  pos_affect
            ;negAffect =  neg_affect } p =
      let p = G.int_of_pLavel p in
      let () = (PMap.iter
                  (fun q i ->
                    let q = G.int_of_pLavel q in
                    match  pos_table.(q) with
                    |Fixed _-> ()
                    |AllFixable (n,map) -> pos_table.(q) <-  AllFixable ((n - i),map);
                    |_ -> ())
                  pos_affect.(p) )
      in
      let () = (PMap.iter
                  (fun q i ->
                    let q = G.int_of_pLavel q in
                    match  neg_table.(q) with
                    |Fixed _ ->  ()
                    |AllFixable (n, map) -> neg_table.(q) <-  AllFixable ((n - i),map);
                    |_ -> ())
                  neg_affect.(p) )      
      in
      pos_table.(p) <- Fixed pos_table.(p);
      neg_table.(p) <- Fixed neg_table.(p) 

  (* この時点で、pをunfixしたことによる、fixableLevelの変化は反映されていないといけない *)
    let unfix {posTable = pos_table
              ;negTable =  neg_table
              ;posAffect =  pos_affect
              ;negAffect =  neg_affect } p =
      let p = G.int_of_pLavel p  in
      let () = (PMap.iter
                  (fun q i ->
                    let q = G.int_of_pLavel q in
                    match  pos_table.(q) with
                    |Fixed _-> ()
                    |AllFixable (n,map) -> pos_table.(q) <-  AllFixable ((n + i),map);
                    |_ -> assert false)
                  pos_affect.(p) )
      in
      let () = (PMap.iter
                  (fun q i ->
                    let q = G.int_of_pLavel q in
                    match  neg_table.(q) with
                    |Fixed _ ->  ()
                    |AllFixable (n,map) -> neg_table.(q) <-  AllFixable ((n + i),map);
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
        

    (* partial -> allfiable
       zero -> allfixable
       にupdateするときは特別, affect mapを必要とするため *)       
    let pos_update2allfixable t p (othere_unknown_map: int PMap.t) =
      let pos_table = t.posTable in
      match pos_table.(G.int_of_pLavel p) with
      |Fixed _ | AllFixable _ ->
        invalid_arg "pos_update2allfixable: decreasing update"
      |PartialFixable |ZeroFixable ->
        let unknown_count =
          PMap.fold
            (fun _ i acc -> i+ acc)
            othere_unknown_map
            0
        in
        pos_table.(G.int_of_pLavel p) <- AllFixable (unknown_count, othere_unknown_map);
        update_affect t.posAffect p othere_unknown_map

    let neg_update2allfixable t p (othere_unknown_map: int PMap.t) =
      let neg_table = t.negTable in
      match neg_table.(G.int_of_pLavel p) with
      |Fixed _ | AllFixable _ ->
        invalid_arg "neg_update2allfixable: decreasing update"
      |PartialFixable |ZeroFixable ->
        let unknown_count =
          PMap.fold
            (fun _ i acc -> i+ acc)
            othere_unknown_map
            0
        in
        neg_table.(G.int_of_pLavel p) <- AllFixable (unknown_count, othere_unknown_map);
        update_affect t.negAffect p othere_unknown_map        

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
        
    let pos_update t p fixable_level =
      let pos_table = t.posTable in
      match pos_table.(G.int_of_pLavel p) with
      |Fixed _ -> invalid_arg "pos_update:attempt to update fixed predicate "
      |AllFixable (n, map) ->
        remove_affect t.posAffect p map;
        update_table pos_table p fixable_level
      |PartialFixable |ZeroFixable ->
        update_table pos_table p fixable_level


    let neg_update t p fixable_level =
      let neg_table = t.negTable in
      match neg_table.(G.int_of_pLavel p) with
      |Fixed _ -> invalid_arg "neg_update:attempt to update fixed predicate "
      |AllFixable (n, map) ->
        remove_affect t.negAffect p map;
        update_table neg_table p fixable_level
      |PartialFixable |ZeroFixable ->
        update_table neg_table p fixable_level
             
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
    |UpBound {senv = senv; env = env; vars = vars; bound = (delta, phi) } ->  (* env|- p -> \phi *)
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

    |LowBound {senv = senv; env = env; vars = vars; bound = phi } ->  (* env|- p -> \phi *)
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
                       ;pending_subst: Formula.subst
                       ;pending_sort_subst: Formula.sort_subst
                       ;position: pPosition
                       }
           |Bound of {waitNum: int ref (* waitNum >= 1 *)
                     ;firstWaitNum: int
                     ;senv:Formula.Senv.t
                     ;pending_sort_subst: Formula.sort_subst
                     ;bound: bound}
           |Fixable of (Polarity.t * bound)


  let unbound_to_bound p_env = function
    |UnBound {waitNum = n
             ;senv = senv
             ;pending_subst = sita
             ;pending_sort_subst = sort_sita
             ;position = position } when !n = 0 ->
      match position with
      |Positive {env = cons_env; negFormula = e1 } ->
        (match Liq.env_sffix cons_env env with
         |None -> invalid_arg "Solver.unbound_to_bound: cons_env and env mismatch"
         |Some local_env ->
           
        
       
      
                     
                   
  let try_to_fix assign = function
    |Fixable (pol,bound) ->
      Some (qformula_of_bound assign bound)
    |_ ->
      None


  let decr_wait_num graph p c = function
    |Fixable _ -> invalid_arg "Fixability.decr_wait_num: can not decrement"
    |Bound {waitNum = wait_num; firstWaitNum = _; bound = bound } ->
      let () = decr wait_num in
      if !wait_num = 0 then
        let new_wait_num = calc_wait_num bound in
        if new_wait_num = 0 then
          (match bound with
           |UpBound _ -> Some (Fixable (Polarity.neg, bound))
           |LowBound _ -> Some (Fixable (Polarity.pos, bound))
          )
        else
          let () = wait_num := new_wait_num in
          None
      else
        (let () = assert (!wait_num > 0) in
         None)
    |UnBound wait_num ->
      let () = decr wait_num in
      if !wait_num = 0 then
        let new_bound  = mk_bound in (* ここは面倒そう,boundを構成する *)
        Some new_bound
      else
        None

  
end


module FixabilityManager = struct
  
  exception Cons_pred_mismatch
          
  type t = {table: ((G.pLavel * G.cLavel), Fixability.t Stack.t) Hashtbl.t
           ;affect: ((G.pLavel * G.cLavel), G.pLavel list) Hashtbl.t }
  (* (p,c) ->q,q',...
     pがfixした時に,constraint cでpを待っているpredicate
   *)

  let decr_wait_num graph q c fixability_stack
                    ~may_change:(pfixable_counter, pfix_state, queue) = 
    let fixability = Stack.top fixability_stack in
    match Fixability.decr_wait_num graph q c fixability with
    |Some new_fixability ->
      (Stack.push new_fixability fixability_stack);
      (match new_fixability with
       |Fixability.Fixable (pol,_) ->
         PFixableConstraintCounter.add_fixable pfixable_counter q pol
                                               ~may_change:(pfix_state, queue)
       |_ -> ())
    |None -> ()
           

  let tell_constraint_predicate_is_fixed t graph assign p c
                                         ~may_change:(pfixable_counter, pfix_state, queue) =
    List.iter
      (fun q -> let stack = (Hashtbl.find t.table (q,c)) in
                decr_wait_num graph q c stack ~may_change:(pfixable_counter, pfix_state, queue)
      )
    (Hashtbl.find t.affect (p,c))



  let try_to_fix t assign p c =
    let fixability_stack = Hashtbl.find t.table (p, c) in
    Fixablility.try_to_fix assign (Stack.top fixability_stack)
         
    (*  pがfixしたことをcsに電波, csはunfix *)
    let fix t graph assign p priority
            ~may_change:(cfix_state, pfix_state, pfixable_counter, queue) =
      if priority.Priority.pol = Polarity.pos then
        List.fold_left
          (fun acc c ->
            if CFixState.is_fixed cfix_state c then
              acc               (* do nothing *)
            else
              (match try_to_fix t assign p c with
               |Some qformula ->
                 let () = CFixState.fix cfix_state p c
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
