open Extensions
open Constraint

module Liq = Type
           
  
   
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

module GComponens = Graph.Components.Make(G)

(* 有向グラフ からDAGが誘導できるような、vertexのリストを取ってくる　*)
(* g is multiple elements conected component *)
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
  
module GTopological = Graph.Topological.Make(G)


  
(* 連結成分: nodeの *)
let rec qsolution_list_for_component  (nodes, (component_sub_graph, starting_nodes)) =
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
  let init_formulas = (List.map Qe.f (qformula_solution_for_pos_cons@qformula_solution_for_nega_cons))@hint_formula_list in
  (p, init_formulas)
  
  
  
let init_assignment_for_starting_node_list objective_predicate nodes starting_nodes =
  List.fold_left
    (fun acc_map starting_node ->
      let p, init_formulas =
        init_assignment_for_starting_node objective_predicate nodes starting_node in
      M.add p init_formulas acc_map)
    M.empty
    starting_nodes



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

    
    
  let must_refine obj_ps assign cons = 
    match sort_of_scons obj_ps assign cons with
    |NotYet -> false
    |MustSat ->
      let fixed_cons = fix_p_to_check_sat assign cons
      in
      not (Constraint.is_satisifiable_simple_cons_all fixed_cons)
    |MustValid ->
      let fixed_cons = fix_p_to_check_valid assign cons in
      not (Constraint.is_valid_simple_cons_all fixed_cons)

      
  (* refine assign cons  *)
  let refine obj_ps assign cons_sort cons =
      match cons_sort with
      |NotYet -> assign
               
      |MustSat ->
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
           {start_nodes =  M.add p (Formula.and_list qs') assign.start_nodes
           ;inter_nodes =  M.empty
           ;inter_nodes_qsolutions =  assign.inter_nodes_qsolutions
           ;yet_qe_qsolutions = assign.inter_nodes_qsolutions
           }
            
         |_  -> assert false
        )

      |MustValid ->
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
           {start_nodes =  M.add p (Formula.and_list qs') assign.start_nodes
           ;inter_nodes =  M.empty
           ;inter_nodes_qsolutions =  assign.inter_nodes_qsolutions
           ;yet_qe_qsolutions = assign.inter_nodes_qsolutions
           }
         | _ -> assert false)
        
          
end
                  
let find_invalid objective_predicate cs_pool assignment qfree_map =
  1

          
let rec iter_refine obj_ps (assign:Assignments.t) cs_pool left_cs =
  match left_cs with
  |consref :: othere ->
    (match ConsPool.consRef_get consref with
     |None -> iter_refine obj_ps assign othere
     |Some cons ->


       
  
let solve_component objecitve_predicates cs_pool (nodes, (component_sub_graph, starting_nodes)) =
  let assignment = init_assignment_for_starting_node_list objective_predicatesnodes starting_nodes in
  let qsolution_list = qsolution_list_for_component (nodes, (component_sub_graph, starting_nodes)) in
  iter_refine objective_predicates cs_pool qsolution_list M.empty assignment

(* cs_poolを見ながらやって行くのが一番単純だし、そこまでコストもなさそうなので良いかな *)
  
  
  
  
  

  
  
  (*   g: 　　　　　　predicate graph
   components: 対象の強連結成分のnodes*)
(* let mk_qformula_assoc  (g:G.t) components = *)
(*   let map = *)
(*     List.fold_left *)
(*       (fun acc_map (nodes, (component_sub_graph, starting_nodes)) -> *)
(*         solve_componens_by_quntifiyers acc_map (nodes, (component_sub_graph, starting_nodes))) *)
(*       M.empty *)
(*       components *)
(*   in *)
(*   map *)
  
  

let f p_hint_map objective_predicate_list cs =
  let cs_pool, pcs = PredicateCons.of_scons_list p_hint_map cs in
  let graph = G.of_predicateCons_list objective_predicate_list pcs in
  (* compute strongly connected components: 強連結成分分解 
     リストはトポロジカルオーダーになることが保証されている
   *)
  let component_list:PredicateCons.t list list =
    GComponens.scc_list(graph)
  in
  let component_with_starting_nodes_list =
    List.map
      (fun nodes ->
        let component_sub_graph = G.sub_graph graph nodes in
        let starting_nodes = choose_vertexs_to_induce_DAG component_sub_graph in
        (nodes, (component_sub_graph, starting_nodes)))
      component_list
  in
  1
  
