open Extensions
open Constraint
module Liq = Type

exception InValid of Constraint.simple_cons
exception UnSat of Constraint.simple_cons
                 
                 
module ConsPool:
sig

  (* ConsPool.consRef型を持つ値は、ConsGen.importされた要素を参照することが保証される
　   ∵ importによってしか、consRef型をもつ値を生成できない
   *)
  type consRef
  val consRef_get : consRef -> (Constraint.simple_cons option)
  val consRef_set : consRef -> (Constraint.simple_cons option) -> unit
  val consRef_set_none : consRef -> unit

  (* val consRef_valid : consRef -> bool *)

  val import : Constraint.simple_cons list ->  consRef list
  type t = consRef list

  val filter_valid : t -> unit
    
  val get_scons_list : t -> Constraint.simple_cons list

  val substitute : Formula.t M.t -> t -> unit

  val filter_none : t -> t
    
end = struct
  
  type consRef =   (Constraint.simple_cons option) ref
  let consRef_get = (!)
  let consRef_set = (:=)

  let consRef_set_none cref =
    cref := None

  type t = consRef list
         
  let import:Constraint.simple_cons list ->  t =
    (fun sc ->
      List.map (fun c ->  ref (Some c)) sc)


  let filter_valid (cs_pool:t) =
    List.iter
      (fun consRef ->
        match !consRef with
        |None -> ()
        |Some cons ->
          let unknown_ps = Constraint.unknown_p_in_simple_cons cons in
          if S.is_empty unknown_ps then
            if Constraint.is_valid_simple_cons_all cons then
              consRef := None
            else
              raise (InValid cons)
          else
            ()
      )
      cs_pool
    
    
  let get_scons_list cs_pool =
    List.map consRef_get cs_pool |> List.flatten_opt_list

  let substitute sita cs_pool =
    List.iter
      (fun consRef ->
        match !consRef with
        |None -> ()
        |Some cons ->
          let cons' = Constraint.subst_simple_cons sita cons in
          consRef := Some cons'
      )
      cs_pool

  let filter_none cs_pool  =
    List.filter (fun consRef -> !consRef <> None) cs_pool
    
end
    
module PredicateCons:
sig
  
  type t = private {
               name : Id.t;
               env : Liq.env;
               wellformed_env : Formula.Senv.t;
               hints : Formula.t list; (* userから与えられるヒント *)
               
               positive_cons : ConsPool.consRef list;
               negative_cons : ConsPool.consRef list;
               othere_cons :  ConsPool.consRef list;
             }
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool

  val get_positive_cons :  t -> Constraint.simple_cons list

  val get_negative_cons :  t -> Constraint.simple_cons list

  val get_othere_cons :  t -> Constraint.simple_cons list        
    
  val of_scons_list : (Formula.t list) M.t -> Constraint.simple_cons list -> ConsPool.t * t list
  val dependency : t list -> t -> t list
    
end = struct

  type t =  {name: Id.t    (* unknown predicate　のid *)
            ;env: Liq.env  (* unknown predicate が生成された時のenv *)
            ;wellformed_env: Formula.Senv.t
            ;hints : Formula.t list (* userから与えられるヒント *)
            ;positive_cons : ConsPool.consRef list
            ;negative_cons : ConsPool.consRef list
            ;othere_cons :  ConsPool.consRef list
            }

  (* Sig.COMPARABE to make graph
     val compare : t -> t -> int
     val hash : t -> int
     val equal : t -> t -> bool
   *)
  let compare t1 t2 = Pervasives.compare t1.name t2.name

  let hash t = Hashtbl.hash t.name

  let equal t1 t2 = t1.name = t2.name


  let get_positive_cons node =
    node.positive_cons
    |> List.map ConsPool.consRef_get 
    |> List.flatten_opt_list

  let get_negative_cons node =
    node.negative_cons
    |> List.map ConsPool.consRef_get 
    |> List.flatten_opt_list

  let get_othere_cons node =
    node.othere_cons
    |> List.map ConsPool.consRef_get 
    |> List.flatten_opt_list    
    
    
    
  let rec extract_envs = function
    |(SSub _):: _ -> invalid_arg "Solver.extract_envs"      
    |SWF (env, (senv, phi)) :: left ->
      let p_envs_list = Formula.list_and phi
                        |> List.filter (function |Formula.Unknown (inner_senv, sort_sita, sita, p) ->
                                                   (assert (sort_sita = M.empty && sita = M.empty));
                                                   senv = inner_senv (* check if this well form cons is most strict one *)
                                                 |_ -> false)
                        |> List.map (function |Formula.Unknown (inner_senv, _, _, p) ->
                                                (p, (env, inner_senv))
                                              | _ -> assert false )
      in
      p_envs_list@(extract_envs left)
    |[] -> []

  let rec (extract_consts_map:
             ConsPool.t 
           -> (ConsPool.consRef list M.t * ConsPool.consRef list M.t  *  ConsPool.consRef list M.t)
           -> (ConsPool.consRef list M.t * ConsPool.consRef list M.t  *  ConsPool.consRef list M.t) )
        
    = (fun cs_pool (pos_map, nega_map, othere_map) ->
      match cs_pool with
      |[] -> (pos_map, nega_map, othere_map)      
      |consRef :: others ->
        (match ConsPool.consRef_get consRef with
         |None -> invalid_arg "Solver.extract_const_map"
         |Some (SWF _) -> invalid_arg "Solver.extract_const_map"
         |Some scons ->
           let pos_ps, nega_ps, othere_ps = Constraint.positive_negative_unknown_p scons in
           let new_pos_map = S.fold
                               (fun  p map -> M.add_list_map p consRef map)
                               pos_ps
                               pos_map                  
           in
           let new_nega_map = S.fold
                                (fun  p map -> M.add_list_map p consRef map)
                                nega_ps
                                nega_map                  
           in
           let new_othere_map = S.fold
                                  (fun  p map -> M.add_list_map p consRef map)
                                  othere_ps
                                  othere_map                  
           in      
           extract_consts_map others (new_pos_map, new_nega_map, new_othere_map)
        )
    )
    


    
  let of_scons_list p_hint_map cs = 
    (assert (List.for_all Constraint.is_predicate_normal_position cs));
    let cs_pool = ConsPool.import cs 
    in

    let wf_cs, sub_cs = List.partition (function |SWF _ -> true |SSub _ -> false) cs in
    let env_senv_list = extract_envs wf_cs in
    
    (* DEBUG:
       check env_senv_list have one entry for each unknow predicate in constraint list cs *)
    let all_p_set =             
      List.fold_left S.union S.empty (List.map Constraint.unknown_p_in_simple_cons cs) in
    (assert (S.for_all (fun p -> (List.length (List.assoc_all p env_senv_list)) = 1) all_p_set));
    (* end DEBUG *)
    let pos_map, nega_map, othere_map = extract_consts_map cs_pool (M.empty, M.empty, M.empty) in
    let tlist =  List.map
                   (fun (p, (env, senv)) ->
                     let hints = try (M.find p p_hint_map) with Not_found -> [] in
                     let positive_cons = M.find_defo p [] pos_map in
                     let negative_cons = M.find_defo p [] nega_map in
                     let othere_cons   = M.find_defo p [] othere_map in
                     {name = p
                     ;env = env
                     ;wellformed_env = senv
                     ;hints = hints
                     ;positive_cons = positive_cons (* [.....] -> p *)
                     ;negative_cons = negative_cons (* [...p...] -> ... *)
                     ;othere_cons = othere_cons (* [...p...] -> p *)
                   })
                   env_senv_list
    in
    (cs_pool,tlist)

  let dependency_id t =
    let positive_cons =  t.positive_cons
                         |>List.map ConsPool.consRef_get
                         |> List.flatten_opt_list
    in
    (* let negative_cons =  t.negative_cons *)
    (*                      |> List.map ConsPool.consRef_get *)
    (*                      |> List.flatten_opt_list *)
    (* in     *)
    let othere_cons =  t.othere_cons
                       |> List.map ConsPool.consRef_get
                       |> List.flatten_opt_list
    in
    if t.othere_cons = [] then
      (* とりあえずpositive_cons　に出現する他のpredicate全て
       *)
      let p_in_pos_cons = List.fold_left
                            (fun acc scons ->
                              S.union acc (Constraint.unknown_p_in_simple_cons scons))
                            S.empty
                            positive_cons
      in
      S.remove t.name p_in_pos_cons
    else
      (* depend on t.name itself *)
      let p_in_pos_cons = List.fold_left
                            (fun acc scons ->
                              S.union acc (Constraint.unknown_p_in_simple_cons scons))
                            S.empty
                            positive_cons
      in
      (* let p_in_nega_cons = List.fold_left *)
      (*                   (fun acc scons -> *)
      (*                     S.union acc (Constraint.unknown_p_in_simple_cons scons)) *)
      (*               S.empty *)
      (*                   negative_cons *)
      (* in *)
      let p_in_othere_cons = List.fold_left
                               (fun acc scons ->
                                 S.union acc (Constraint.unknown_p_in_simple_cons scons))
                               S.empty
                               othere_cons
      in
      (assert (S.mem t.name p_in_othere_cons));
      S.union p_in_pos_cons p_in_othere_cons
      

  (*　pがqに依存している =def= [...q...] -> p という形のconstraintがある　*)
  let dependency ts t  =
    let depend_name = dependency_id t |> S.elements in
    List.map
      (fun name -> List.find
                     (fun  pc -> pc.name = name)
                     ts)
      depend_name


    

end
    

module QSolution =              (* predicate unkonwn のqunatifyer付きの解 *)
  struct
    type t = Or of Formula.qformula list
                 
    (* input: positive constraint for p in normal form
       \Gamma;.. -> p
       \Gamma;.. .. -> p
       ...
     *)
    let qsolution_for_cons_list env p positive_cs =
      Or (List.map (Constraint.mk_qformula_from_positive_cons env p) positive_cs)

      
    let qsolution_for_pnode node =
      if node.PredicateCons.othere_cons <> [] then invalid_arg "solver.predicateCons.mk_qformula"
      else
        let pos_cs = List.map ConsPool.consRef_get node.PredicateCons.positive_cons
                     |> List.flatten_opt_list
        in
        let qsolution = qsolution_for_cons_list node.env node.name pos_cs in
        (* set None to solved constraint *)
        let () = List.iter ConsPool.consRef_set_none node.PredicateCons.positive_cons in
        qsolution

    let qe = function
      |Or qformula_list ->
        let formula_list = List.map Qe.f qformula_list in
        Formula.or_list formula_list


        
  end

(* input:  phi -> (unknown_p1 /\ unknown_p2 /\ phi1 /\ phi2 )

     output: phi -> unknown_p1,
             phi -> unknown_p2,     
             phi -> phi1 /\ phi2
 *)
let rec decompose_result_of_implication = function
  |SWF _ -> invalid_arg "Solver.decompose_result_of_implication"
  |SSub (env, phi1, result) ->
    let unknown_p_list, others =
      Formula.list_and result
      |> List.partition (function |Formula.Unknown _ -> true
                                  | _                -> false
                        )
    in
    let unknown_p_sub_cons_list = List.map (fun p -> SSub (env, phi1, p)) unknown_p_list in
    let ohthers_p_sub_cons = SSub (env, phi1, (Formula.and_list others)) in
    ohthers_p_sub_cons :: unknown_p_sub_cons_list
    


    
(* graph predicate *)
module G = struct

  module G = Graph.Persistent.Digraph.ConcreteBidirectional(PredicateCons)
  module GComponens = Graph.Components.Make(G)
  include G

  let add_edge_v2vlist graph v vlist = 
    List.fold_left (fun acc_g v_dst -> add_edge acc_g v v_dst) empty vlist

  let add_edge_vlist2v graph vlist v = 
    List.fold_left (fun acc_g v_src -> add_edge acc_g v_src v) empty vlist

  let remove_vertex_list g vlist =
    List.fold_left remove_vertex g vlist

  let mem_vertex_list g vlist =
    List.for_all (G.mem_vertex g) vlist

  let sub_graph g vlist =
    List.fold_left
      (fun acc_g v ->
        if not (List.mem v vlist) then
          remove_vertex acc_g v
        else
          acc_g)
      g
      vlist
    

  let has_cycle g =
    let components = GComponens.scc_list g in
    List.exists (fun component -> (List.length component >= 2)) components
    
  let of_predicateCons_list (objective_ps: Id.t list) (pcs:PredicateCons.t list) =
    (* remve objective predicate from node of graph *)
    let nodes = List.filter (fun pc -> List.mem pc.PredicateCons.name objective_ps) pcs in
    List.fold_left
      (fun acc_graph node ->
        let depend_nodes = PredicateCons.dependency pcs node in
        let acc_graph = G.add_vertex acc_graph node         in
        add_edge_vlist2v acc_graph depend_nodes node )
      empty
      nodes


  let of_scons_list p_hint_map obj_ps cs =
    let cs_pool, pcs =  PredicateCons.of_scons_list p_hint_map cs in
    let graph = of_predicateCons_list obj_ps pcs in
    graph, cs_pool

  let self_loop_nodes g =
    fold_vertex
      (fun node acc_self_loop_nodes ->
        if mem_edge g node node then
          node::acc_self_loop_nodes
        else
          acc_self_loop_nodes
      )
      g
      []

  let max_degree_node g =
    let (max_degree, max_node_opt) =
      G.fold_vertex
        (fun node (max_degree, max_node_opt) ->
          let degree = (G.out_degree g node) + (G.in_degree g node) in
          if degree > max_degree then
            (degree, Some node)
          else
            (max_degree, max_node_opt))
        g
        (-1, None)
      
    in
    match max_node_opt with
    |None -> invalid_arg "max_degree_node: empty graph"
    |Some node -> node
                
end




(* componentを解く時に持ち回す、assignment *)
module Assignments:
sig
  
  type t =  {start_nodes: Formula.t M.t
            ;inter_nodes: Formula.t M.t                
            ;inter_nodes_qsolutions : (Id.t * QSolution.t) list (* topological order *)
            ;yet_qe_qsolutions :  (Id.t * QSolution.t) list     (* suffix of inter_nodes_qsolutions *)
            }
          
  type consSort = |NotYet | MustValid | MustSat

  val sort_of_scons : Id.t list -> t -> Constraint.simple_cons -> consSort

  val substitute : t -> Constraint.simple_cons -> Constraint.simple_cons

  val init : Formula.t M.t -> (Id.t * QSolution.t) list -> t

  val get_predicate_map : t -> Formula.t M.t

  val refine : Id.t list  -> t  -> Constraint.simple_cons -> t option

  val qe_and_get_next : t -> t option
    
end = struct
  
  type t =  {start_nodes: Formula.t M.t
            ;inter_nodes: Formula.t M.t                
            ;inter_nodes_qsolutions : (Id.t * QSolution.t) list (* topological order *)
            ;yet_qe_qsolutions :  (Id.t * QSolution.t) list     (* suffix of inter_nodes_qsolutions *)
            }
          
  type consSort = |NotYet | MustValid | MustSat

  let sort_of_scons obj_ps assign cons =
    let p_in_cons = Constraint.unknown_p_in_simple_cons cons in
    let start_map = assign.start_nodes in
    let inter_map = assign.inter_nodes in
    let exist_obj_ps = S.exists (fun p -> List.mem p obj_ps) p_in_cons in
    let exist_unfix_ps = S.exists (fun p -> not ((M.mem p start_map) || (M.mem p inter_map))) p_in_cons in
    if exist_unfix_ps then
      NotYet
    else if exist_obj_ps then
      MustSat
    else
      MustValid

  let substitute assign cons =
    cons
    |> Constraint.subst_simple_cons assign.start_nodes
    |> Constraint.subst_simple_cons assign.inter_nodes

  let find_start_node p assign =
    M.find p assign.start_nodes

  let fix_p_to_check_sat assign cons =
    cons
    |> substitute assign
    |> Constraint.replace_unknown_p_to_top

  let fix_p_to_check_valid assign cons = substitute assign cons

  let init start_node_assign qsolution_list =
    {start_nodes = start_node_assign
    ;inter_nodes = M.empty
    ;inter_nodes_qsolutions = qsolution_list
    ;yet_qe_qsolutions = qsolution_list
    }

  let get_predicate_map assign =
    if assign.yet_qe_qsolutions <> [] then invalid_arg "Assignments.get_predicate_map: yet qe"
    else
      M.union (fun p _ _ -> assert false) assign.start_nodes assign.inter_nodes
    
  let refine obj_ps assign cons = 
    match sort_of_scons obj_ps assign cons with
    |NotYet -> None
             
    |MustSat ->
      let fixed_cons = fix_p_to_check_sat assign cons
      in
      let must_refine = not (Constraint.is_satisifiable_simple_cons_all fixed_cons)
      in
      if not must_refine then None
      else
        (match cons with
         |Constraint.SSub (_, _, Formula.Unknown (_, _, _, p)) -> (* この位置に来るのは、starting_nodeのみ *)
           let qs = try find_start_node p assign
                        |> Formula.list_and
                    with Not_found -> assert false
           in
           let qs' = List.filter
                       (fun q ->
                         let p_to_q = M.singleton p q in
                         let cons' = Constraint.subst_simple_cons p_to_q cons in
                         let fixed_cons' = fix_p_to_check_sat assign cons' in
                         (Constraint.is_satisifiable_simple_cons_all fixed_cons')
                       )
                       qs
           in
           Some {start_nodes =  M.add p (Formula.and_list qs') assign.start_nodes
                ;inter_nodes =  M.empty
                ;inter_nodes_qsolutions =  assign.inter_nodes_qsolutions
                ;yet_qe_qsolutions = assign.inter_nodes_qsolutions
                }
           
         |_  -> raise (UnSat cons)
        )

      
    |MustValid ->
      let fixed_cons = fix_p_to_check_valid assign cons in
      let must_refine = not (Constraint.is_valid_simple_cons_all fixed_cons)
      in
      if not must_refine then None
      else
        (match cons with
         |Constraint.SSub (_, _, Formula.Unknown (_, _, _, p)) -> (* この位置に来るのは、starting_nodeのみ *)
           let qs = try find_start_node p assign
                        |> Formula.list_and
                    with Not_found -> assert false
           in
           let qs' = List.filter
                       (fun q ->
                         let p_to_q = M.singleton p q in
                         let cons' = Constraint.subst_simple_cons p_to_q cons in
                         let fixed_cons' =  fix_p_to_check_valid assign cons' in
                         (Constraint.is_valid_simple_cons_all fixed_cons')
                       )
                       qs
           in
           Some {start_nodes =  M.add p (Formula.and_list qs') assign.start_nodes
                ;inter_nodes =  M.empty
                ;inter_nodes_qsolutions =  assign.inter_nodes_qsolutions
                ;yet_qe_qsolutions = assign.inter_nodes_qsolutions
                }
         | _ -> raise (InValid cons))
      

  let qe_and_get_next assign =
    match assign.yet_qe_qsolutions with
    |(p, qsolution) :: othere ->
      let p_formula = QSolution.qe qsolution in
      Some {start_nodes = assign.start_nodes
           ;inter_nodes =  M.add p p_formula assign.inter_nodes (* add *)
           ;inter_nodes_qsolutions =  assign.inter_nodes_qsolutions
           ;yet_qe_qsolutions = othere (* pop *)
           }
    |[] -> None
         
end

module GComponens = Graph.Components.Make(G)

(* 有向グラフ からDAGが誘導できるような、vertexのリストを取ってくる　*)
(* g is multiple elements conected component *)

module PredicateComponent = struct
  
  type t =
    {nodes : G.vertex list
    ;sub_graph : G.t
    ;start_nodes : G.vertex list
    }
    
  let rec choose_vertexs_to_induce_DAG_rec (g:G.t) = 
    let max_degree_node = G.max_degree_node g in
    let g_minus = G.remove_vertex g max_degree_node in
    let g_minus_components = GComponens.scc_list g_minus in
    let chosen_vertex_g_minus = List.map
                                  (fun component ->
                                    if List.length component <= 1 then
                                      []
                                    else
                                      let sub_g = G.sub_graph g_minus component in
                                      choose_vertexs_to_induce_DAG_rec sub_g
                                  )
                                  g_minus_components
                                |>
                                  List.concat
    in
    max_degree_node::chosen_vertex_g_minus
    
  (* 有向グラフ からDAGが誘導できるような、vertexのリストを取ってくる　*)
  (* g is multiple elements conected component *)
    
  let choose_vertexs_to_induce_DAG (g:G.t) = 
    let self_loop_nodes = G.self_loop_nodes g in
    let g_minus = G.remove_vertex_list g  self_loop_nodes in
    let g_minus_components = GComponens.scc_list g_minus in
    let chosen_vertex_g_minus = List.map
                                  (fun component ->
                                    if List.length component <= 1 then
                                      []
                                    else
                                      let sub_g = G.sub_graph g_minus component in
                                      choose_vertexs_to_induce_DAG_rec sub_g
                                  )
                                  g_minus_components
                                |>
                                  List.concat  
    in
    self_loop_nodes@chosen_vertex_g_minus


  let of_graph (g:G.t) =
    let g_components_list = GComponens.scc_list(g) in
    List.map
      (fun nodes ->
        let component_sub_graph = G.sub_graph g nodes in
        let starting_nodes = choose_vertexs_to_induce_DAG component_sub_graph in
        {nodes = nodes
        ;sub_graph = component_sub_graph
        ;start_nodes = starting_nodes
        }
      )
      g_components_list
    
    
  module GTopological = Graph.Topological.Make(G)


                      
  (* 連結成分: nodeの *)
  let rec qsolution_list_for_component {nodes=nodes
                                       ;sub_graph=component_sub_graph
                                       ;start_nodes = starting_nodes
                                       } =
    (assert (G.mem_vertex_list component_sub_graph nodes ));
    let dag = G.remove_vertex_list component_sub_graph starting_nodes in
    (assert (not (G.has_cycle dag)));
    GTopological.fold
      (fun node qsolution_acc ->
        let qsolution = QSolution.qsolution_for_pnode node in
        (* add to tail of list
          to make resulting qformula_assc be topological order *)
        qsolution_acc@[node.PredicateCons.name, qsolution])
      dag
      []

  let init_assignment_for_starting_node objective_predicate node_in_component starting_node =
    let p = starting_node.PredicateCons.name in    
    let env = starting_node.PredicateCons.env in
    let hint_formula_list = starting_node.PredicateCons.hints in
    let pos_cons = PredicateCons.get_positive_cons starting_node in
    let nega_cons = PredicateCons.get_negative_cons starting_node in
    let is_independent_cons cons = (* objective_predicate以外のunknown predicateが出てこないか*)
      S.for_all
        (fun unknown_p -> (List.mem unknown_p objective_predicate))
        (S.remove p (Constraint.unknown_p_in_simple_cons cons))
    in
    let independent_pos_cons = List.filter is_independent_cons pos_cons in
    let independent_nega_cons = List.filter is_independent_cons nega_cons in
    
    
    
    let qformula_solution_for_pos_cons =
      List.map (Constraint.mk_qformula_from_positive_cons env p) independent_pos_cons in
    let qformula_solution_for_nega_cons =
      List.map (Constraint.mk_qformula_from_negative_cons env p) independent_nega_cons in
    let init_formula_list = (List.map Qe.f (qformula_solution_for_pos_cons@qformula_solution_for_nega_cons))@hint_formula_list in
    ( p, Formula.and_list init_formula_list )
    
    
    
  let init_assignment_for_starting_node_list objective_predicate component =
    let nodes = component.nodes in
    let starting_nodes = component.start_nodes in
    List.fold_left
      (fun acc_map starting_node ->
        let p, init_formulas =
          init_assignment_for_starting_node objective_predicate nodes starting_node in
        M.add p init_formulas acc_map)
      M.empty
      starting_nodes


    
    
  let rec iter_refine obj_ps (assign:Assignments.t) cs_list left_cs =
    match left_cs with
    |cons :: othere ->
      (match Assignments.refine obj_ps assign cons with
       |None -> iter_refine obj_ps assign cs_list othere
       |Some new_assign -> iter_refine obj_ps new_assign cs_list cs_list (* 振り出しに戻る *)
      )
    |[] ->
      (match Assignments.qe_and_get_next assign with
       |None -> assign
       |Some new_assign -> iter_refine obj_ps new_assign cs_list cs_list (* iteration *)
      )
     
     
     
  let solve obj_ps cs_pool component =
    let start_node_assign = init_assignment_for_starting_node_list obj_ps component in
    let qsolution_list = qsolution_list_for_component component in 
    let init_assign = Assignments.init start_node_assign qsolution_list in
    let cs_list = ConsPool.get_scons_list cs_pool in 
    let refined_assign = iter_refine obj_ps init_assign cs_list cs_list in
    Assignments.get_predicate_map refined_assign

end


let solve_graph obj_ps cs_pool graph =
  let pcomponent_list = PredicateComponent.of_graph graph in
  (* 強連結成分がトポロジカルオーダーに並んでいる。先頭から解いていけば良い。 *)
  let solution = List.fold_left
                   (fun acc_map  p_component->
                     let () = ConsPool.filter_valid cs_pool in (* unknown pが含まれていないものは解いておく *)                     
                     let component_solution =
                       PredicateComponent.solve obj_ps cs_pool p_component
                     in
                     let () = ConsPool.substitute component_solution cs_pool in (* 解決したunknown pを代入 *)
                     component_solution)
                   M.empty
                   pcomponent_list
  in
  solution
                          
let f ~hints:p_hint_map ~objective_predicates:obj_ps ~constraints:cs =
  let graph, cs_pool = G.of_scons_list p_hint_map obj_ps cs in
  let map_except_obj_ps = solve_graph obj_ps cs_pool graph in 
  (* cs_poolを更新する副作用によって、この時点でcs_poolにはobj_ps以外のunknown pは存在しない *)
  let cs' = ConsPool.get_scons_list cs_pool in
  let graph', cs_pool' = G.of_scons_list p_hint_map [] cs' in
  let map_obj_ps = solve_graph [] cs_pool' graph' in
  M.union (fun _ _ _ -> assert false) map_except_obj_ps map_obj_ps

                                            
