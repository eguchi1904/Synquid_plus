open Extensions
module Liq = Type
module G = ConsGraph.G           
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
module CSet = ConsGraph.CSet
            
module PNode:sig
  type t = G.pLavel
  val of_pLavel : G.pLavel -> t
    
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool

end= struct
  
  type t = G.pLavel
         
  let of_pLavel t = t
         
  let compare = compare
  let hash p = (G.int_of_pLavel p)
  let equal = (=)

            
end



(* predicateだけからなるグラフ *)
(* \Gamma|- pが、
   \Gamma; p; q -> ... 
   の時　p -neg-> q
 *)
module PG = struct
  module BaseG = Graph.Persistent.Digraph.ConcreteBidirectional(PNode)
  module Components = Graph.Components.Make(BaseG)
  include BaseG
        
  let add_edge_v2vlist pg_graph v vlist = 
    List.fold_left (fun acc_g v_dst -> BaseG.add_edge acc_g v v_dst) pg_graph vlist
    
  let add_edge_vlist2v pg_graph vlist v = 
    List.fold_left (fun acc_g v_src -> BaseG.add_edge acc_g v_src v) pg_graph vlist

  let add_edge_vlist2vlist pg_graph src_list dest_list =
    List.fold_left
      (fun acc src -> add_edge_v2vlist acc src dest_list)
      pg_graph
    src_list


  let add_dependecy_from_c p2pnode pg_graph =function     (* (negS.t, pos_list)  *)
    |Constraint.SSub (env, e1, e2) ->
      let p_e1 = Formula.extract_unknown_p e1 in
      let p_e2 = Formula.extract_unknown_p e2 in
      let p_e1_list = S.elements p_e1 |> List.map p2pnode in
      let p_e2_list = S.elements p_e2 |> List.map p2pnode in
      add_edge_vlist2vlist pg_graph p_e1_list p_e2_list
    |Constraint.SWF _ -> pg_graph      
      
      
  let of_graph graph :t=
    let p2pnode = (fun p ->  G.pLavel_of_id graph p |> PNode.of_pLavel) in
    let pg_graph = G.fold_p
                     (fun p_lav (acc:t) ->
                       BaseG.add_vertex acc p_lav)
                     graph
                 BaseG.empty
    in
    G.fold_c
      (fun c_lav (acc:t) ->
        let c = G.cons_of_cLavel graph c_lav in
        add_dependecy_from_c p2pnode acc c)
      graph
      pg_graph
            

end

let rec prop_up p pg_graph (tord: PNode.t -> int) escape_ps  acc_ps =
  if PSet.mem p acc_ps || PSet.mem p escape_ps then
    acc_ps
  else
    let () = assert (PG.mem_vertex pg_graph p) in (* pがここでない *)
    let acc_ps = PSet.add p acc_ps in
    PG.fold_succ
      (fun q acc->
        if tord p = tord q then
          acc
        else
          let () = assert (tord p > tord q) in
          prop_up q pg_graph tord escape_ps acc 
      )
      pg_graph
      p
      acc_ps
    
    
let rec prop_down p pg_graph (tord: PNode.t -> int) escape_ps acc_ps = 
  if PSet.mem p acc_ps || PSet.mem p escape_ps then
    acc_ps
  else
    let acc_ps = PSet.add p acc_ps in
    PG.fold_pred
      (fun q acc->
        if tord p = tord q then
          acc
        else
          let () = assert (tord p < tord q) in 
          prop_down q pg_graph tord escape_ps acc)
      pg_graph
      p
      acc_ps    
    

let extend_direction pg_graph (tord: PNode.t -> int) up_ps down_ps =
  let up_ps' =
    PSet.fold (fun p acc -> prop_up p pg_graph tord down_ps acc) up_ps PSet.empty
  in
  (* downのpropはしない *)
  (* let down_ps' = *)
  (*   PSet.fold (fun p acc -> prop_down p pg_graph tord up_ps' acc) down_ps PSet.empty *)
  (* in *)
  up_ps', down_ps


let prop_direction ~may_change:graph up_ps down_ps =
  let up_ps = PSet.of_id_Set graph up_ps in
  let down_ps = PSet.of_id_Set graph down_ps in  
  let pg_graph = PG.of_graph graph in
  let _,tord = PG.Components.scc pg_graph in
  let up_ps', down_ps'  = extend_direction pg_graph tord up_ps down_ps in
  let () = assert (PSet.subset up_ps up_ps') in
  let () = assert (PSet.equal down_ps down_ps') in  
  let () = PSet.iter (G.update_direction2up graph) up_ps' in
  (* let () = PSet.iter (G.update_direction2down graph) down_ps' in *)
  let up_ps' = PSet.fold
                 (fun p acc -> S.add (G.id_of_pLavel graph p) acc)
                 up_ps'
                 S.empty
  in
  let down_ps' = PSet.fold
                 (fun p acc -> S.add (G.id_of_pLavel graph p) acc)
                 down_ps'
                 S.empty
  in
  up_ps', down_ps'
  

 
  


          
