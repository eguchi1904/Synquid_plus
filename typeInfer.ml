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
(* annotation *)
(* -------------------------------------------------- *)

let adjust_refine dinfos ((alist,ty_ml):Ml.schema) ty_refine :Liq.schema=
  let sita = Ml.unify2 (Ml.shape ty_refine) ty_ml in
  let ty_refine' = Ml.subst_refine_ty dinfos sita ty_refine in
  let () = assert ((Ml.subst_ty sita ty_ml) = ty_ml) in
  (alist, [], ty_refine')
  

let rec adjust_annotation dinfos (t_ml:Ml.schema TaSyn.t) (t_user_anno:Liq.t option TaSyn.t) =
  let open TaSyn in
  match t_ml, t_user_anno with
  |PLet ((x, ml_sch), t1_ml, t2_ml),
   PLet ((y, None), t1_usr, t2_usr) when (x = y) ->
    let t1' = adjust_annotation dinfos t1_ml t1_usr in
    let t2' = adjust_annotation dinfos t2_ml t2_usr in
    PLet ((x, Ml.mk_refine_ignore_sch dinfos ml_sch), t1', t2')

  |PLet ((x, ml_sch), t1_ml, t2_ml),
   PLet ((y, Some liq_ann), t1_usr, t2_usr) when (x = y) ->
    let t1' = adjust_annotation dinfos t1_ml t1_usr in
    let t2' = adjust_annotation dinfos t2_ml t2_usr in
    PLet ((x, adjust_refine dinfos ml_sch liq_ann), t1', t2')

  |PE e_ml, PE e_usr -> PE (adjust_annotation_e dinfos e_ml e_usr)

  |PI b_ml, PI b_usr -> PI (adjust_annotation_b dinfos b_ml b_usr)

  |PF f_ml, PF f_usr -> PF (adjust_annotation_f dinfos f_ml f_usr)

  |PHole, PHole -> PHole

  |_ -> invalid_arg "adjust_annotation: syntax mismatch"

and adjust_annotation_e dinfos e_ml e_usr =
  match e_ml, e_usr with
  |PSymbol (x, ml_schs), PSymbol (y, usr_ann_opts) when x = y ->
    let _, schs = List.fold_right
                   (fun ml_sch (acc_usr_ann_opts, acc) ->
                     match acc_usr_ann_opts with
                     |None :: usr_ann_opts' ->
                       (usr_ann_opts',
                        (Ml.mk_refine_ignore_sch dinfos ml_sch)::acc)
                     |Some usr_ann :: usr_ann_opts' ->
                       (usr_ann_opts',
                        (adjust_refine dinfos ml_sch usr_ann)::acc)
                     |[] -> ([], Ml.mk_refine_ignore_sch dinfos ml_sch::acc))
                   ml_schs
                   (usr_ann_opts, [])
    in
    PSymbol (x, schs)

  |PAuxi (g, ml_sch), PAuxi (g', None) when g = g' ->
    PAuxi (g, Ml.mk_refine_ignore_sch dinfos ml_sch)

  |PAuxi (g, ml_sch), PAuxi (g', Some liq_anno) when g = g' ->
    PAuxi (g, adjust_refine dinfos ml_sch liq_anno)

  |PInnerFun f_ml, PInnerFun f_usr ->
    PInnerFun (adjust_annotation_f dinfos f_ml f_usr)

  |PAppFo (e1_ml, e2_ml), PAppFo (e1_usr, e2_usr) ->
    let e1' = adjust_annotation_e dinfos e1_ml e1_usr in
    let e2' = adjust_annotation_e dinfos e2_ml e2_usr in
    PAppFo (e1', e2')

  |PAppHo  (e1_ml, f2_ml), PAppHo (e1_usr, f2_usr) ->
    let e1' = adjust_annotation_e dinfos e1_ml e1_usr in
    let f2' = adjust_annotation_f dinfos f2_ml f2_usr in
    PAppHo (e1', f2')

  |_ -> invalid_arg "adjust_annotation_e: syntax mismatch"

and adjust_annotation_b dinfos b_ml b_usr =
  match b_ml, b_usr with
  |PIf (e1_ml, t2_ml, t3_ml), PIf (e1_usr, t2_usr, t3_usr) ->
    let e1' = adjust_annotation_e dinfos e1_ml e1_usr in
    let t2' = adjust_annotation dinfos t2_ml t2_usr in
    let t3' = adjust_annotation dinfos t3_ml t3_usr in
    PIf (e1', t2', t3')

  |PMatch (e1_ml, cases_ml), PMatch (e1_usr, cases_usr) ->
    let e1' = adjust_annotation_e dinfos e1_ml e1_usr in
    let cases' = List.map2 (adjust_annotation_case dinfos) cases_ml cases_usr in
    PMatch (e1', cases')

  |_ -> invalid_arg "adjust_annotation_b: sytax mismatch"

and adjust_annotation_case dinfos case_ml case_usr =
  let args =                    
    List.map
      (fun (x, ml_sch) -> (x, Ml.mk_refine_ignore_sch dinfos ml_sch))
      case_ml.argNames
  in
  let t' = adjust_annotation dinfos case_ml.body case_usr.body in
  {constructor = case_ml.constructor
  ;argNames = args
  ;body = t'
  }

and adjust_annotation_f dinfos f_ml f_usr =
  match f_ml, f_usr with
  |PFun ((x, ml_sch), t_ml),
   PFun ((y, None), t_usr) when x = y ->
    let t' = adjust_annotation dinfos t_ml t_usr in
    PFun ((x, Ml.mk_refine_ignore_sch dinfos ml_sch), t')
  |PFun ((x, ml_sch), t_ml),
   PFun ((y, Some usr_ty), t_usr) when x = y ->
    let t' = adjust_annotation dinfos t_ml t_usr in
    PFun ((x, adjust_refine dinfos ml_sch usr_ty), t')

  |PFix _, PFix _ -> assert false

  |_ -> invalid_arg "adjust_annotation_f: syntax mismatch"
   
    

                  
(* -------------------------------------------------- *)
(* main *)
(* -------------------------------------------------- *)  
let extract_goal ta_t =
  let auxi_ty_map = TaSyn.get_auxi_anno ta_t
                  |> M.map Liq.schema2ty
                in
  let up_ps, neg_ps =
    M.fold
      (fun g ty (acc_pos, acc_neg) ->
        let pos_ps, neg_ps, _ = Liq.positive_negative_unknown_p ty
        in
        (S.union pos_ps acc_pos), (S.union neg_ps acc_neg) )
      auxi_ty_map
      (S.empty, S.empty)
  in
  (auxi_ty_map, up_ps, neg_ps)


(* let f:T = .. in..contents
の、T中のunknown predicateを集める
 *)
let extract_outer (ta_t:Liq.schema TaSyn.t) =
  TaSyn.fold_let_anno
    (fun x sch (up_ps_out, down_ps_out) ->
      let pos_ps, neg_ps, othere_ps = Liq.positive_negative_unknown_p (Liq.schema2ty sch) in
      (assert (S.is_empty othere_ps));
      ((S.union up_ps_out pos_ps), (S.union down_ps_out neg_ps)))
    ta_t
  (S.empty, S.empty)
  
  
    
let liqInfer z3_env dinfos qualifiers env ta_t =
  let st_infer = Sys.time () in
  (print_string (TaSyn.syn2string Liq.schema2string ta_t));
  let ta_t', tmp, cs, cs_ann = ConsGen.cons_gen_infer dinfos env ta_t in
  let () = Format.printf "\ntasyn:\n%s\n\n"
                         (TaSyntax.syn2string Liq.schema2string_sort ta_t')
  in  
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs)
                  |> Constraint.remove_dummy_loop
                  |> Constraint.add_dummy_start_point_constraint
  in
  let simple_cs_ann = List.concat (List.map split_cons cs_ann)
                      |> Constraint.remove_ignore                    
  in
  let simple_cs = simple_cs_ann@simple_cs in
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
  (print_string (TaSyn.syn2string Liq.schema2string ta_t));
  let (ta_t', cs, cs_ann) = ConsGen.cons_gen_check dinfos env ta_t req_ty in
  let () = Printf.printf "\ntasyn:\n%s\n\n"
                         (TaSyntax.syn2string Liq.schema2string_sort ta_t')
  in
  let auxi_ty_map, up_ps, neg_ps = extract_goal ta_t' in
  let up_ps_out, down_ps_out = extract_outer ta_t' in
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs)
                  |> Constraint.remove_dummy_loop
                  |> Constraint.add_dummy_start_point_constraint                
  in
  let simple_cs_ann = List.concat (List.map split_cons cs_ann)
                      |> Constraint.remove_ignore

  in    
  let () = (Printf.printf "cs_length:%d \n" (List.length cs)) in
  let () =  (Printf.printf "simple_cs_length:%d \n" (List.length simple_cs)) in
  (* (print_string (scons_list_to_string simple_cs)); *)

  (* let const_var_sita = Liq.mk_subst_for_const_var env in *)
  (* let p_candi = init_p_assignment const_var_sita qualifiers simple_cs S.empty in *)
  (* logging *)
    try
      (* let p_assign = ConsSolver.find_predicate z3_env qualifiers simple_cs env req_ty in *)
      let p_assign = Solver.f up_ps neg_ps up_ps_out down_ps_out qualifiers (simple_cs_ann@simple_cs) in
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


let f  z3_env dinfos qualifiers env (t: Liq.t option TaSyn.t) =
  let ml_option_t =
    TaSyn.access_annotation_t
      (function Some ty -> Some (Ml.shape ty) |None -> None)
    t
  in
  let (ta_ml, ml_ty) = Ml.infer (Ml.shape_env env) ml_option_t in
  let ta_t = adjust_annotation dinfos ta_ml t in
  liqInfer z3_env dinfos qualifiers env ta_t
  

let f_check z3_env dinfos qualifiers env (t: Liq.t option TaSyn.t) (_,_,req_ty)=
  let ml_option_t =
    TaSyn.access_annotation_t
      (function Some ty -> Some (Ml.shape ty) |None -> None)
      t
  in
  let ta_ml = Ml.check (Ml.shape_env env) ml_option_t (Ml.shape req_ty) in
  let () = print_string ("**after ml_inference**\n\n"
                         ^(TaSyn.syn2string Ml.string_of_sch ta_ml)
                         ^"\n\n")
  in
  let ta_t = adjust_annotation dinfos ta_ml t in
  let () = print_string ("**after adjust annotation**\n\n"
                         ^(TaSyn.syn2string Liq.schema2string ta_t)
                         ^"\n\n")
  in  
  liqCheck z3_env dinfos qualifiers env ta_t req_ty
  
(* -------------------------------------------------- *)
(* inference of E-term *)
(* -------------------------------------------------- *)
  
let liqInferEterm z3_env dinfos qualifiers env ta_e =
  (* (print_string (TaSyn.syn2string Ml.string_of_sch ta_t)); *)
  let (ta_e', Liq.TLet(cenv, tmp), cs, cs_ann) = cons_gen_e dinfos env Liq.env_empty ta_e in
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
  let e = TaSyn.add_empty_annotation_e e in
  match Ml.infer (Ml.shape_env env) (TaSyntax.PE e) with
  |(TaSyn.PE ta_ml_e), ml_ty ->
    let ta_e = adjust_annotation_e dinfos ta_ml_e e in
    liqInferEterm z3_env dinfos qualifiers env ta_e
  | _ -> assert false

