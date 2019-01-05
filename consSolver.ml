open Extensions
open Qualifier
open ConsGen
open Constraint
   
module Liq = Type
module TaSyn = TaSyntax



(* log file *)


let solving_och = open_out "solving.log"
             

let log_assingment mes pcandi =
  let pcandi_list = M.bindings pcandi in
  let pcandi_str =
        String.concat "\n"
                  (List.map (fun (k_i, e_list) ->
                       let e_list_str = String.concat
                                      "; "
                                      (List.map Formula.p2string e_list)
                       in
                       Printf.sprintf
                         "  %s -> [ %s ]"
                         k_i
                         e_list_str
                     )
                            pcandi_list
                  )
  in
  Printf.fprintf
    solving_och
    "%s:\n\n%s\n\n\n\n\n\n\n\n"
    mes
    pcandi_str

let log_refine mes k_list before_pcandi after_pcandi c =
  let before_pcandi_sita =
    M.map Formula.and_list before_pcandi
  in
  let related_unknown_p =
    match c with
    |SSub (env, e, ks) ->      
      S.union (Formula.extract_unknown_p ks)
              (S.union (Formula.extract_unknown_p e)
                       (Liq.env_extract_unknown_p env))
    |SWF (_, (senv, e1)) ->
      Formula.extract_unknown_p e1
  in
  let mk_related_assingment pcandi =
    List.map
      (fun k_i -> (k_i, M.find k_i pcandi))
      (S.elements related_unknown_p)
  in
  let mk_related_assingment_str related_assingment =
    String.concat "\n"
                  (List.map (fun (k_i, e_list) ->
                       let e_list_str = String.concat
                                      "; "
                                      (List.map Formula.p2string e_list)
                       in
                       Printf.sprintf
                         "  %s -> [ %s ]"
                         k_i
                         e_list_str
                     )
                            related_assingment
                  )
  in
  let before_related_assingment_str = mk_related_assingment_str (mk_related_assingment before_pcandi) in
  let after_related_assingment_str =  mk_related_assingment_str (mk_related_assingment after_pcandi) in
  
  Printf.fprintf
    solving_och
    "\n%s\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\nbefore:\n%s\nconstraint:\n%s\nafter:\n%s\n\n"
    mes
    before_related_assingment_str
    (scons2string_human before_pcandi_sita c)
    after_related_assingment_str

(* -------------------------------------------------- *)
(* unknown predicate assignments *)
(* -------------------------------------------------- *)        
type p_assign = (Formula.t list) M.t

let add_p_assign (pcandi:p_assign) (p_i:Id.t) (e:Formula.t) =
   try
    let candi = M.find p_i pcandi in
    if e = Formula.Bool true then
      pcandi
    else
      M.add p_i (e::candi) pcandi
  with
    Not_found ->
    if e = Formula.Bool true then
      M.add p_i [] pcandi
    else
      M.add p_i [e] pcandi


let subst_inv (sita:Formula.subst) :Formula.subst =
  M.fold
    (fun x p inv_sita ->
      match p with
      |Formula.Var (s,y) -> M.add y (Formula.Var (s,x)) inv_sita
      |_ -> inv_sita)
    sita
  M.empty

  
(* let rec init_p_assignment' (cs:simple_cons list) (pcandi:p_assign) = *)
(*   match cs with *)
(*   |SSub (env, Formula.Unknown _, Formula.Unknown _) :: cs' ->  *)
(*   (\* raise (Invalid_argument "predicateunknown vs predicateunknown") *\) *)
(*     init_p_assignment' cs' pcandi *)
(*   |SSub (env, Formula.Unknown (sita, i), e) :: cs' *)
(*        when S.is_empty (Formula.extract_unknown_p e)-> *)
(*     let sita_inv = subst_inv sita in *)
(*     let e' = Formula.substitution sita_inv e in *)
(*     init_p_assignment' cs' (add_p_assign pcandi i e') *)
(*   |SSub (env, e, Formula.Unknown (sita, i)) :: cs' *)
(*           when S.is_empty (Formula.extract_unknown_p e) -> *)
(*     let sita_inv = subst_inv sita in *)
(*     let e' = Formula.substitution sita_inv e in     *)
(*     init_p_assignment' cs' (add_p_assign pcandi i e') *)
(*   |_ :: cs' -> init_p_assignment' cs' pcandi *)
(*   |[] -> *)
(*     pcandi *)

let rec extend_qualifiers cs (qs: Qualifier.t list) =
  match cs with
  |SSub (env, Formula.Unknown _, Formula.Unknown _) :: cs' -> 
  (* raise (Invalid_argument "predicateunknown vs predicateunknown") *)
    extend_qualifiers cs' qs
  |SSub (env, Formula.Unknown (sort_sita, sita, i), e) :: cs'
       when S.is_empty (Formula.extract_unknown_p e)->
    (* let sita_inv = subst_inv sita in *)
    (* let e' = Formula.substitution sita_inv e in *)
    extend_qualifiers cs' ((Qualifier.formula_to_qualifier e)::qs)
  |SSub (env, e, Formula.Unknown (sort_sita, sita, i)) :: cs'
          when S.is_empty (Formula.extract_unknown_p e) ->
    (* let sita_inv = subst_inv sita in *)
    (* let e' = Formula.substitution sita_inv e in *)
    extend_qualifiers cs' ((Qualifier.formula_to_qualifier e)::qs)
  |_ :: cs' -> extend_qualifiers cs' qs
  |[] -> qs




let rec k_positive_pos cs = match cs with
  |SSub (env, e1, e2) :: cs' ->
    let env_formula = Liq.env2formula env (S.union (Formula.fv e1) (Formula.fv e2)) in
    let e2_list = Formula.list_and e2 in
    let k_set_e2 = List.fold_left
                  (fun acc e -> match e with
                                 |Formula.Unknown (_,_, i) -> S.add i acc
                                 |_ -> acc)
                   S.empty
                   e2_list
    in
    let premise_list = (Formula.list_and env_formula)@(Formula.list_and e1) in
    let k_set_premise = List.fold_left
                          (fun acc e -> match e with
                                        |Formula.Unknown (_,_, i) -> S.add i acc
                                        |_ -> acc)
                          S.empty
                          premise_list
    in
    let positive_k = S.diff k_set_e2 k_set_premise in
    S.union positive_k (k_positive_pos cs')
  | SWF _ ::cs' -> k_positive_pos cs'
  |[] -> S.empty
    
                                   
(* 
supported_ks: this predicate will be assigned "true" if it occurs negatively

 *)
let rec init_p_assignment const_var_sita (qualifiers: Qualifier.t list) (cs:simple_cons list) supported_ks =
  let debug_qulify = List.map (Qualifier.qualifier_to_formula) qualifiers in
  let qualifiers = Qualifier.refine_qualifiers const_var_sita (extend_qualifiers cs qualifiers) in
  let debug_qulify = List.map (Qualifier.qualifier_to_formula) qualifiers in
  (* kset: set of all predicate unknowns in cs *)
  let k_set = List.fold_left
                (fun acc scons -> S.union acc (unknown_p_in_simple_cons scons))
                S.empty
                 cs
  in
  let p_assign = List.fold_left
                   (fun acc c ->
                     match c with
                     |SWF (_, (senv, Formula.Unknown (sort_sita, sita, k))) ->
                       let p_list = List.concat (List.map (gen_p_candidate const_var_sita senv k) qualifiers) in
                       let () = log_assingment ("in fold:"^k) acc in 
                       M.add k p_list acc
                     |_ -> acc)
                   M.empty
                   cs
  in
  let () = log_assingment "line756" p_assign in
  let k_set_list = S.elements k_set in
  let p_assign_list = M.bindings p_assign in
  (assert (S.for_all (fun k -> M.mem k p_assign) k_set));
  let p_assign = M.map (List.uniq_f Formula_eq.f) p_assign in
  let p_assign = M.map
                   (fun p_list -> List.filter (fun p -> UseZ3.satisfiable_but_not_valid (fst (UseZ3.convert p))) p_list)
               p_assign
  in
  let k_negative_set = S.diff k_set (k_positive_pos cs) in
  S.fold
    (fun  k_negative acc ->
      if S.mem k_negative supported_ks then
        M.add k_negative [] acc
      else
        M.add k_negative [Formula.Bool false] acc
    )
    k_negative_set
    p_assign

(* -------------------------------------------------- *)
(* constraints solving *)
(* -------------------------------------------------- *)
exception RefineErr of (Formula.t list) * string
exception SolvingErr of string



    
let rec isnt_valid z3_env cs p_candi =
  match cs with
  |scons::cs' ->
    let sita = M.map (fun tlist -> Formula.and_list tlist) p_candi in
    let sita_debug = M.bindings sita in
    let scons' = subst_simple_cons sita scons in
    if is_valid_simple_cons z3_env scons' then
      isnt_valid z3_env cs' p_candi
    else
      Some scons
  |[] -> None

       
(* when
 env|- e <: sita_i*qs
 is not valid,
   filater qs -> qs'.
 *)
let filter_qualifiers sita_pcandi env e (sort_sita_i, sita_i, qs) =
   List.filter
     (fun q ->let q' = (Formula.sort_subst2formula sort_sita_i (Formula.substitution sita_i q) ) in
              let p = Formula.substitution
                        sita_pcandi
                        (Formula.Implies ((Formula.And(env,e), q')))
              in
              let z3_p,p_s = UseZ3.convert  p in
              UseZ3.is_valid z3_p)
     qs
  
(* filterしても、自由変数の出現がへり、invalidのままということがありえる *)     
let rec refine z3_env pcandi c =       (* cがvalidになるようにする。 *)
  match c with
  |SSub (env, e, ks) ->
    let k_list = Formula.list_and ks in
    let sita_pcandi = M.map (fun tlist -> Formula.and_list tlist) pcandi in
    let (env_phi,_,_) = inst_scons sita_pcandi c in
  
    let new_pcandi = 
      List.fold_left
        (fun acc e2 ->
          match e2 with
          |Formula.Unknown (sort_sita_i, sita_i, i) ->
            let qs = M.find i pcandi in
            let qs' = filter_qualifiers sita_pcandi env_phi e (sort_sita_i, sita_i, qs) in
            M.add i qs' acc
          | e2 ->
             let phi = Formula.substitution sita_pcandi
                                            (Formula.Implies ((Formula.And (env_phi, e), e2)))
             in
             let z3_phi, phi_s = UseZ3.convert phi in
             if UseZ3.is_valid z3_phi then
               acc
             else
               raise (RefineErr (k_list, "can't refine" ))
        )
        pcandi
        k_list
    in
    let () = log_refine "successfly refined" k_list pcandi new_pcandi c in
    new_pcandi
  |SWF (env, (senv, Formula.Unknown (sort_sita_i, sita_i, i))) ->
    let qs = M.find i pcandi in
    let qs' = List.filter
                (fun q -> let q' = (Formula.sort_subst2formula sort_sita_i (Formula.substitution sita_i q)) in
                          is_valid_simple_cons z3_env (SWF (env,(senv, q'))))
                qs
    in
    M.add i qs' pcandi
  |_ -> raise (RefineErr ([],"can't refine"))
    
        
let rec solve' z3_env (cs:simple_cons list) (p_candi:p_assign) =
  match isnt_valid z3_env cs p_candi with
  |None -> p_candi
  |Some scons ->
    (try
       solve' z3_env cs (refine z3_env p_candi scons)
     with
       RefineErr (k_list,mes) ->
       let () =  log_refine "refinement fail" k_list p_candi p_candi scons in
       let () = close_out solving_och in
       raise (SolvingErr mes)
    )

let rec solve z3_env (cs:simple_cons list) (p_candi:p_assign) =
  let wf_cs,sub_cs = List.partition (function |SWF _ -> true |SSub _ -> false) cs in
  (* first solve well formedness constraint and then subtyping constraints *)
  let p_candi' = solve' z3_env wf_cs p_candi in
  let p_candi'' = solve' z3_env sub_cs p_candi' in
  p_candi''


  
let find_predicate z3_env qualifiers (cs:simple_cons list) env tmp =
  let const_var_sita = Liq.mk_subst_for_const_var env in
  let toplevel_ks = Liq.extract_unknown_p tmp in
  let st = Sys.time () in
  let p_candi = init_p_assignment const_var_sita qualifiers cs toplevel_ks in
  let ed = Sys.time () in
  (Printf.printf "\n\nend_init_p_candi:%f\n\n" (ed -. st ));
    (* logging *)
  let () = log_assingment "initial assignment" p_candi in
  let p_candi_debug = M.bindings p_candi in
  let p_assign = solve z3_env cs p_candi in
  (* logging *)
  let () = log_assingment "solved assignment" p_assign in
  let () = ConsGen.log_simple_cons "solved constraint" cs in
  p_assign
  
