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
    

  val import : Constraint.simple_cons list ->  consRef list
  type t = consRef list
         
end = struct
  
  type consRef =   (Constraint.simple_cons option) ref
  let consRef_get = (!)
  let consRef_set = (:=)
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
               
               positive_cons : ConsPool.consRef list;
               negative_cons : ConsPool.consRef list;
               othere_cons :  ConsPool.consRef list;
      }
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
    
  val of_scons_list : Constraint.simple_cons list -> ConsPool.t * t list
  val dependency : t list -> t -> t list
    
end = struct

  type t =  {name: Id.t    (* unknown predicate　のid *)
            ;env: Liq.env  (* unknown predicate が生成された時のenv *)
            ;wellformed_env: Formula.Senv.t
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
      


         
  let of_scons_list cs = 
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
                     let positive_cons = M.find_defo p [] pos_map in
                     let negative_cons = M.find_defo p [] nega_map in
                     let othere_cons   = M.find_defo p [] othere_map in
                     {name = p
                     ;env = env
                     ;wellformed_env = senv
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
    let negative_cons =  t.negative_cons
                         |> List.map ConsPool.consRef_get
                         |> List.flatten_opt_list

    in    
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
      let p_in_nega_cons = List.fold_left
                        (fun acc scons ->
                          S.union acc (Constraint.unknown_p_in_simple_cons scons))
                    S.empty
                        negative_cons
      in
      let p_in_othre_cons = List.fold_left
                        (fun acc scons ->
                          S.union acc (Constraint.unknown_p_in_simple_cons scons))
                    S.empty
                        othere_cons
      in
      S.union p_in_pos_cons
              p_in_nega_cons
      |>S.union p_in_othre_cons

  let dependency ts t  =
    let depend_name = dependency_id t |> S.elements in
    List.map
      (fun name -> List.find
                     (fun  pc -> pc.name = name)
                     ts)
      depend_name

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

  include Graph.Persistent.Digraph.ConcreteBidirectional(PredicateCons)

  let add_edge_v2vlist graph v vlist = 
    List.fold_left (fun acc_g v_dst -> add_edge acc_g v v_dst) empty vlist

  let add_edge_vlist2v graph vlist v = 
    List.fold_left (fun acc_g v_src -> add_edge acc_g v_src v) empty vlist    
                    

  let of_predicateCons_list (objective_ps: Id.t list) (pcs:PredicateCons.t list) =
    (* remve objective predicate from node of graph *)
    let nodes = List.filter (fun pc -> List.mem pc.PredicateCons.name objective_ps) pcs in
    List.fold_left
      (fun acc_graph node ->
        let depend_nodes = PredicateCons.dependency pcs node
        in
        add_edge_v2vlist (add_vertex acc_graph node)  node depend_nodes)
      empty
      nodes
        
end



let f objective_predicate_list cs =
  let cs_pool, pcs = PredicateCons.of_scons_list cs in
  let predicate_graph = G.of_predicateCons_list objective_predicate_list pcs 
  
         
