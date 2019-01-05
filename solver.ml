open Extensions
open Constraint

module Liq = Type
   
module PredicateCons = struct
  
  type t =  {name: Id.t    (* unknown predicate　のid *)
            ;env: Liq.env  (* unknown predicate が生成された時のenv *)
            ;wellformed_env: (Id.t * Formula.sort) list (* well formed ness *)
            
            ;positive_cons: Constraint.simple_cons list
            ;negative_cons: Constraint.simple_cons list
            ;othere_cons: Constraint.simple_cons list
            }

  let rec extract_envs = function
    |(SSub _):: _ -> invalid_arg "Solver.extract_envs"      
    |SWF (env, (senv, phi)) :: left ->
      let ps = Formula.extract_unknown_p phi |> S.elements in
      let p_envs_list = List.map (fun p -> (p, (env, senv))) ps in
      p_envs_list@(extract_envs left)
    |[] -> []

  let rec extract_consts_map sub_cs (pos_map, nega_map, othere_map) =
    match sub_cs with
    |SWF _ :: _ -> invalid_arg "Solver.extract_const_map"
    |scons :: others ->
      let pos_ps, nega_ps, othere_ps = Constraint.positive_negative_unknown_p scons in
      let new_pos_map = S.fold
                      (fun  p map -> M.add_list_map p scons map)
                      pos_ps
                      pos_map                  
      in
      let new_nega_map = S.fold
                           (fun  p map -> M.add_list_map p scons map)
                           nega_ps
                           nega_map                  
      in
      let new_othere_map = S.fold
                             (fun  p map -> M.add_list_map p scons map)
                             othere_ps
                             othere_map                  
      in      
      extract_consts_map others (new_pos_map, new_nega_map, new_othere_map)
    |[] -> (pos_map, nega_map, othere_map)
      
      
      
      
           
      
      
    

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
                             
      
         
  let of_scons_list cs =
    let wf_cs, sub_cs = List.partition (function |SWF _ -> true |SSub _ -> false) cs in
    let env_senv_list = extract_envs wf_cs in
    let pos_map, nega_map, othere_map = extract_consts_map sub_cs (M.empty, M.empty, M.empty) in
    let tlist =  List.map
                   (fun (p, (env, senv)) ->
                     let positive_cons = M.find_defo p [] pos_map in
                     let negative_cons = M.find_defo p [] nega_map in
                     let othere_cons   = M.find_defo p [] othere_map 
                     in
                     {name = p
                     ;env = env
                     ;wellformed_env = senv
                     ;positive_cons = positive_cons
                     ;negative_cons = negative_cons
                     ;othere_cons = othere_cons
                   })
                   env_senv_list
    in
    tlist
    
end
   
