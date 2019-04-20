open Extensions
open Qualifier

open Constraint
open ConsGen   
open ConsSolver
   
module Liq = Type
module TaSyn = TaSyntax
module Cons = Constraint

exception LiqErr of string
(* log file *)


(* -------------------------------------------------- *)
(* main *)
(* -------------------------------------------------- *)  
let extract_up ta_t =
  let auxi_ty_map = TaSyn.get_auxi_anno ta_t
                  |> M.map Liq.schema2ty
                in
  let up_ps =
    M.fold
      (fun g ty acc ->
        let pos_ps, _, _ = Liq.positive_negative_unknown_p ty
        in
        S.union pos_ps acc)
      auxi_ty_map
      S.empty
  in
  (auxi_ty_map, up_ps)
  
  
  
    
let liqInfer z3_env dinfos qualifiers env ta_t =
  let st_infer = Sys.time () in
  (print_string (TaSyn.syn2string Ml.string_of_sch ta_t));
  let ta_t', tmp, cs = ConsGen.cons_gen_infer dinfos env ta_t in
  let () = Format.printf "\ntasyn:\n%s\n\n"
                         (TaSyntax.syn2string Liq.schema2string_sort ta_t')
  in  
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs) in
  let () = (Printf.printf "cs_length:%d \n" (List.length cs)) in
  let () =  (Printf.printf "simple_cs_length:%d \n" (List.length simple_cs)) in
  (* (print_string (scons_list_to_string simple_cs)); *)
  let p_assign = ConsSolver.find_predicate z3_env qualifiers simple_cs env tmp in
  let sita = M.map (fun tlist -> Formula.and_list tlist) p_assign in
  let ed_infer = Sys.time () in
  let () = (Printf.printf "\n\nLiq_INfer:%f\n\n" (ed_infer -. st_infer )) in
  Liq.substitute_F sita tmp
  
  
let liqCheck z3_env dinfos qualifiers env ta_t req_ty =
  let st_infer = Sys.time () in
  (print_string (TaSyn.syn2string Ml.string_of_sch ta_t));
  let (ta_t', cs) = cons_gen dinfos env ta_t req_ty in
  let () = Printf.printf "\ntasyn:\n%s\n\n"
                         (TaSyntax.syn2string Liq.schema2string_sort ta_t')
  in
  let auxi_ty_map, up_ps = extract_up ta_t' in
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs) in
  let () = (Printf.printf "cs_length:%d \n" (List.length cs)) in
  let () =  (Printf.printf "simple_cs_length:%d \n" (List.length simple_cs)) in
  (* (print_string (scons_list_to_string simple_cs)); *)

  (* let const_var_sita = Liq.mk_subst_for_const_var env in *)
  (* let p_candi = init_p_assignment const_var_sita qualifiers simple_cs S.empty in *)
  (* logging *)
    try
      (* let p_assign = ConsSolver.find_predicate z3_env qualifiers simple_cs env req_ty in *)
      let p_assign = Solver.f up_ps qualifiers simple_cs in
      let auxi_ty_map = M.map (Liq.substitute_F p_assign) auxi_ty_map in
      
    (* logging *)
    (* let () = log_assingment "solved assignment" p_assign in *)
    (* let () = log_simple_cons "solved constraint" simple_cs in *)
    (* let sita = M.map (fun tlist -> Formula.and_list tlist) p_assign in *)
    let ed_infer = Sys.time () in
    let () = (Printf.printf "\n\nLiq_check:%f\n\n" (ed_infer -. st_infer )) in
    Ok (M.bindings auxi_ty_map)
  with
    ConsSolver.SolvingErr mes ->
    let ed_infer = Sys.time () in
    let () = (Printf.printf "\n\n%s Liq_check:%f\n\n" mes (ed_infer -. st_infer )) in
    raise (ConsSolver.SolvingErr mes)


let f  z3_env dinfos qualifiers env t =
  (* let inlined_t = Syntax.inline_rec_fun M.empty t in *)
  let (ta_t, ml_ty) = Ml.infer (Ml.shape_env env) t in
  liqInfer z3_env dinfos qualifiers env ta_t
  

let f_check z3_env dinfos qualifiers env t (_,_,req_ty)=
  (* let inlined_t = Syntax.inline_rec_fun M.empty t in *)
  (* let t = Syntax.alpha M.empty t in *)
  let ta_t = Ml.check (Ml.shape_env env) t (Ml.shape req_ty) in
  (* req_ty を、ml_tyに合わせる必要があるな *)
  (* それか要求を通せる何か、これは辛いな。 *)
  liqCheck z3_env dinfos qualifiers env ta_t req_ty
(* -------------------------------------------------- *)
(* inference of E-term *)
(* -------------------------------------------------- *)
  
let liqInferEterm z3_env dinfos qualifiers env ta_e =
  (* (print_string (TaSyn.syn2string Ml.string_of_sch ta_t)); *)
  let (ta_e', Liq.TLet(cenv, tmp), cs) = cons_gen_e dinfos env ta_e in
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs) in
  (* (print_string (scons_list_to_string simple_cs)); *)
  let p_assign = ConsSolver.find_predicate z3_env qualifiers simple_cs env tmp in
  (* let const_var_sita = Liq.mk_subst_for_const_var env in *)
  (* let p_candi = init_p_assignment const_var_sita qualifiers simple_cs S.empty in *)
  
  (* let p_candi_debug = M.bindings p_candi in *)

  (* let  *)
  (* let p_assign = solve z3_env simple_cs p_candi in *)
  let sita = M.map (fun tlist -> Formula.and_list tlist) p_assign in
  Liq.TLet ((Liq.env_substitute_F sita cenv), Liq.substitute_F sita tmp)


  
let fEterm  z3_env dinfos qualifiers env e =
  match Ml.infer (Ml.shape_env env) (Syntax.PE e) with
  |(TaSyn.PE ta_e), ml_ty ->
    liqInferEterm z3_env dinfos qualifiers env ta_e
  | _ -> assert false

