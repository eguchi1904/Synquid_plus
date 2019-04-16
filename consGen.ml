module Liq = Type
module TaSyn = TaSyntax

open Constraint

let cons_och = open_out "constraints.log"

exception ConsGenErr of string
             
(* -------------------------------------------------- *)
(* logging *)
(* -------------------------------------------------- *)                            
  
let log_tmp mes tmp =
  Printf.fprintf cons_och
                 "%s\n--------------------------------------------------\n%s\n--------------------------------------------------\n"
                 mes (Liq.t2string tmp)

let log_pa_tmp mes ((args, p):Formula.pa) =
  Printf.fprintf cons_och
                 "%s\n--------------------------------------------------\n\..%s\n--------------------------------------------------\n"
                 mes (Formula.p2string p)
  
  
  
let log_cons mes cs =
  Printf.fprintf cons_och "\n\n%s\n" (cons_list_to_string_human cs)

let log_place mes t =
  Printf.fprintf cons_och "\n\n\n\n%s\n|||||||||||||||||||||||||||||||||||||\n%s\n|||||||||||||||||||||||||||||||||||||\n"
                 mes (TaSyntax.syn2string Ml.string_of_sch t)



let log_simple_cons mes cs =
  Printf.fprintf cons_och "%s:**************************************************\n\n%s\n" mes (scons_list_to_string cs)

  

(* -------------------------------------------------- *)
(* auxiliary function  *)
(* -------------------------------------------------- *)

    
(* input :: x1:t1 -> ... -> {B|phi}
   output :: [(x1,t1);...;], phi
 *)

let rec constructor_shape c_t =
  match c_t with
  |Liq.TFun ((x,t1),t2) ->
    let args,ret = constructor_shape t2 in
    (x,t1)::args,ret
  |Liq.TScalar (b,p) ->[],p
  |_ -> assert false
      
    
(* -------------------------------------------------- *)
(* constraints generation *)
(* -------------------------------------------------- *)

let rec fresh senv (data_info_map: Data_info.t M.t) t =
  let open Data_info in
  let senv_with_v_sort =
    try
      Formula.Senv.add
        senv
        Id.valueVar_id
        (Ml.t2sort t)
    with
      Ml.T2SORT -> senv
  in
  match t with
  |Ml.MLBool ->
    Liq.TScalar (Liq.TBool, Formula.genUnkownP senv_with_v_sort "k")
  |Ml.MLInt -> Liq.TScalar (Liq.TInt, Formula.genUnkownP senv_with_v_sort "k")
  |Ml.MLData (i, tys) when M.mem i data_info_map ->
    let tys_tmp = List.map (fresh senv data_info_map) tys in
    let data_info = M.find i data_info_map in
    let pa_shape_list = Data_info.instantiate_pred_param_shape data_info tys_tmp in
    let unknown_pa_list = List.map
                            (fun (s, shape) -> Formula.genUnknownPa_shape senv shape s)
                            pa_shape_list
    in
    
    Liq.TScalar (Liq.TData (i, tys_tmp, unknown_pa_list), Formula.genUnkownP senv_with_v_sort "k")
  |Ml.MLData (i, _) -> assert false
  |Ml.MLVar x -> Liq.TScalar ((Liq.TAny x), Formula.genUnkownP senv_with_v_sort "k") (* TAny i　型 *)
  |Ml.MLFun (ty1, ty2) ->
    let x = Id.genid "x" in
    let new_senv = try Formula.Senv.add senv x (Ml.t2sort ty1) with Ml.T2SORT -> senv in
    Liq.TFun ((x, (fresh senv data_info_map ty1)), (fresh new_senv data_info_map ty2))
      

let mk_tmp dinfos env t =
  let senv = Liq.mk_sort_env env in
  let tmp = fresh senv dinfos (Ml.ta_infer (Ml.shape_env env) t) in
  tmp

            
let rec cons_gen dinfos env t req_ty =
  match t with
  |TaSyn.PLet ((x, (alist, ty)), t1, t2) when S.mem x (TaSyn.fv t1)-> (* recursive def *)
    let new_tmp_x =  fresh (Liq.mk_sort_env env) dinfos ty in
    let new_tmp_x_sch = (alist, [], new_tmp_x) in
    let new_c =  [WF (env, new_tmp_x)] in
    (* logging *)
    let () = log_cons "" new_c in
    let () = log_tmp x new_tmp_x in
    (* disable let polimorphism for predicate *)
    let env2 =  (Liq.env_add_schema env (x, new_tmp_x_sch)) in
    let (t1', c1) = cons_gen dinfos env2 t1 new_tmp_x in
    (* let env2 =  (Liq.env_add env (x, tmp1)) in *)
    let (t2', c2) = cons_gen dinfos env2 t2 req_ty in
    (TaSyn.PLet ((x, new_tmp_x_sch), t1', t2'), new_c@c1@c2)
 |TaSyn.PLet ((x, (alist, ty)), t1, t2) ->
   let new_tmp_x = fresh  (Liq.mk_sort_env env) dinfos ty in
   let (t1', c1) = cons_gen dinfos env t1 new_tmp_x in
    (* disable let polimorphism for predicate *)
   let new_tmp_x_sch = (alist, [], new_tmp_x) in
   let new_c =  [WF (env, new_tmp_x)] in
   (* logging *)
   let () = log_cons "" new_c in
   let () = log_tmp x new_tmp_x in
   let env2 =  (Liq.env_add_schema env (x, new_tmp_x_sch )) in
    (* let env2 =  (Liq.env_add env (x, tmp1)) in *)
   let (t2', c2) = cons_gen dinfos env2 t2 req_ty in
   (TaSyn.PLet ((x, new_tmp_x_sch), t1',t2'), new_c@c1@c2)
   
 |TaSyn.PE e ->
   let (e', (Liq.TLet (c_env, tmp_e)), c) = cons_gen_e dinfos env e in
   let new_c = [Sub ((Liq.env_append env c_env), tmp_e, req_ty)] in
   let () = log_cons "" new_c in
   (TaSyn.PE e', new_c@c )
 |TaSyn.PI b ->
   let b', c = cons_gen_b dinfos env b req_ty in
   (TaSyn.PI b', c)
 |TaSyn.PF f ->
   let f', c = cons_gen_f dinfos env f req_ty in
   (TaSyn.PF f', c)
  |TaSyn.PHole -> assert false

and cons_gen_e dinfos env e =
  match e with
  |TaSyn.PAppFo (e1, e2) ->
    (match cons_gen_e dinfos env e1 with
     (* e1 :: x:tmp_in -> tmp_out *)
     |e1', (Liq.TLet (c_env1, (Liq.TFun ((x, tmp_in), tmp_out) ) )), c1 ->
       let open Formula in
       let e2', Liq.TLet (c_env2, tmp2), c2 = cons_gen_e dinfos env e2 in
       (match tmp2 with
        | Liq.TScalar (b, Eq (Var (_, valvar), e2_value))
             when  valvar = Id.valueVar_id ->
           let tmp_out' = Liq.substitute_F (M.singleton x e2_value) tmp_out in
           let c_env = (Liq.env_append c_env1 c_env2)  in
           let new_c = [(Sub (Liq.env_append env (Liq.env_append c_env1 c_env2), tmp2, tmp_in))] in
           (* logging *)
           let e1_ty_str =  (Liq.t2string_sort (Liq.TFun ((x, tmp_in), tmp_out) )) in
           let () = log_place(Printf.sprintf "application:%s" e1_ty_str) (TaSyntax.PE e) in 
           let () = log_cons "" new_c in
           (TaSyn.PAppFo (e1',e2'),
            (Liq.TLet (c_env, tmp_out')),
            new_c@(c1@c2)
           )
        | Liq.TScalar (b, Eq (e2_value, (Var (_, valvar))))
             when  valvar = Id.valueVar_id ->
           let tmp_out' = Liq.substitute_F (M.singleton x e2_value) tmp_out in
           let c_env = (Liq.env_append c_env1 c_env2)  in
           let new_c = [(Sub (Liq.env_append env (Liq.env_append c_env1 c_env2), tmp2, tmp_in))] in
           (* logging *)
           let e1_ty_str =  (Liq.t2string_sort (Liq.TFun ((x, tmp_in), tmp_out) )) in           
           let () = log_place (Printf.sprintf "application:%s" e1_ty_str)  (TaSyntax.PE e) in 
           let () = log_cons "" new_c in
           (TaSyn.PAppFo (e1',e2'),
            (Liq.TLet (c_env, tmp_out')),
            new_c@(c1@c2)
           )
        | Liq.TScalar (b, tmp2_phi) ->   
           (* 引数をフレッシュ *)
           let b_sort = (match Liq.b2sort b with Some s -> s|_ -> assert false) in
           let x' =  Id.genid x in
           let x'_var = Formula.Var (b_sort, x') in
          let tmp_out' = Liq.substitute_F (M.singleton x x'_var) tmp_out in (* [x'/x]t1_out *)
          (* たすver *)
          (* let c_env =  (Liq.env_add (Liq.env_append c_env1 c_env2) (x',tmp2)) in *)
          let c_env =  (Liq.env_add (Liq.env_append c_env1 c_env2) (x',tmp2)) in
          (* ad hook extractしたときに、必ずx'が引き抜かれるように *)
          (* let c_env = (Liq.env_add  (Liq.env_append c_env1 c_env2) *)
          (*                             (Formula.substitution *)
          (*                                (M.singleton Id.valueVar_id x') tmp2_phi)) *)
          (* in *)
          let new_c =[Sub (Liq.env_append env (Liq.env_append c_env1 c_env2), tmp2, tmp_in)] in
          
          (* logging *)
          let e1_ty_str =  (Liq.t2string_sort (Liq.TFun ((x, tmp_in), tmp_out) )) in           
           let () = log_place (Printf.sprintf "application:%s" e1_ty_str)  (TaSyntax.PE e) in           
          let () = log_cons "" new_c in
          (TaSyn.PAppFo (e1',e2'),
           (Liq.TLet (c_env, tmp_out')),
           new_c@(c1@c2)
          )
        | Liq.TFun _ -> assert false
        | Liq.TBot -> assert false
       )
       
     |e2',(Liq.TLet (_, ty)), _ ->
       (Printf.printf "exspect:function type but got\n%s" (Liq.t2string ty));
       assert false
    )
  |TaSyn.PAppHo (e1, f1)  ->
    let tmp_f1 =  fresh (Liq.mk_sort_env env) dinfos (Ml.ta_infer_f (Ml.shape_env env) f1)  in
    let (f1', c_f1) = cons_gen_f dinfos env f1 tmp_f1 in
    (match cons_gen_e dinfos env e1 with
     |e1', (Liq.TLet (c_env1, Liq.TFun ((x, tmp_in), tmp_out) )), c_e1 ->
       let new_c =    [(Sub (Liq.env_append env c_env1, tmp_f1, tmp_in));
                       WF (env, tmp_f1)]
       in
       (* logging *)
       let () = log_place "application(higher order)" (TaSyntax.PE e) in 
       let () = log_tmp "appHO arg" tmp_f1 in
       let () = log_cons "" new_c in
       (TaSyn.PAppHo (e1', f1'),
         Liq.TLet (c_env1, tmp_out),
        new_c@(c_f1@c_e1)
       )
     |_ -> assert false
    )
   
  |TaSyn.PSymbol (x, schs) ->     (* x[t1,t2,...tn] explicite instantiation *)

    let tys = List.map Ml.ty_in_schema schs in
    let x_liq_sch =
      try Liq.env_find env x with Not_found -> (print_string x);assert false
    in
    (match x_liq_sch with
     |([], [], Liq.TScalar (b, _)) ->
       let open Formula in
       (match Liq.b2sort b with
        |Some b_sort ->
          (TaSyn.PSymbol (x, []),
            Liq.TLet (Liq.env_empty, Liq.TScalar (b, (Eq
                                                       (Var (b_sort, Id.valueVar_id),
                                                        Var (b_sort, x))))),
           [])
        |None ->  raise (ConsGenErr "dont know what sort is this"))
       
     |(alist, plist, ty_x) ->
       let () = Printf.printf "\n env_sch\n%s::%s. %s" x (String.concat "," alist) (Liq.schema2string x_liq_sch) in
       let a_sort_sita =
         List.fold_left2
           (fun acc_sita a sch ->
             (try let sch_sort = Ml.t2sort (Ml.ty_in_schema sch) in
                  M.add a sch_sort acc_sita
              with _ -> acc_sita)
           )
           M.empty
           alist
           schs
       in
     (* p_sort_var = p中のsort variable *)
     (* a_sch_dec = List.combine alist schs *)
     (* a:sort_var -> alist, *)
       let plist =              (* instantiate plist *)
         List.map
           (fun (p, shape) -> (p, (Formula.sort_subst_to_shape a_sort_sita shape )))
           plist
       in
       let unknown_pa_list: Formula.pa list = 
         List.map
           (fun (p, (arg_sort, rets)) ->
             let (args, body) = Formula.genUnknownPa_shape  (Liq.mk_sort_env env) (arg_sort, rets) p in
             (* make well formedness constraints *)
             (args, body)
           )
           plist
       in

       (* typeのinstantiate *)
       let tys_tmp = List.map (fresh (Liq.mk_sort_env env) dinfos) tys in
       let ty_x' = Liq.instantiate_implicit x_liq_sch tys_tmp unknown_pa_list in
       (* ty_x'のwell formedness: ここで、新しく生成したunknown_paなどのwellformednessが保証される *)
       let wellformedness_ty_x' = WF (env, ty_x') in       
       let  a_sort_sita_list = M.bindings a_sort_sita in
       let () = Printf.printf "a_list_sort:%s"
                              (String.concat ","
                                             ((List.map
                                                (fun (i, sort) -> Printf.sprintf "%s->%s"
                                                                                i
                                                                                (Formula.sort2string sort))
                                                a_sort_sita_list)))
       in
       let () = Printf.printf "\nunknwon_pa:%s"
                              (String.concat ""
                                             ((List.map Formula.pa2string_detail) unknown_pa_list))
       in
       let () = Printf.printf "\nvar_instants:\n%s::%s" x (Liq.t2string ty_x') in
       (* logging *)
       let () = List.iter (log_pa_tmp ("instantiate:"^x)) unknown_pa_list in
       let () = List.iter (log_tmp ("instantiate:"^x)) tys_tmp in
       let new_c =  [wellformedness_ty_x'] in
       let () = log_cons "" new_c in
       let schs_tmp = List.map Liq.mk_mono_schmea tys_tmp in
       (TaSyn.PSymbol (x, schs_tmp), (* Formula.tのinstantiateの情報が入っていない *)
         Liq.TLet (Liq.env_empty, ty_x'),
         new_c))

  |TaSyn.PInnerFun f_in ->
     let tmp_f =  fresh (Liq.mk_sort_env env) dinfos (Ml.ta_infer_f (Ml.shape_env env) f_in)  in
     let (f_in', c_f) = cons_gen_f dinfos env f_in tmp_f in
     let new_c = [WF (env, tmp_f)] in
  (* logging *)
     let () = log_place "inner function" (TaSyntax.PF f_in) in
     let () = log_tmp "inner function" tmp_f in
     let () = log_cons "" new_c in
     (TaSyn.PInnerFun f_in',
      Liq.TLet (Liq.env_empty, tmp_f),
      new_c@c_f)
     
  |TaSyn.PAuxi (g, sch) ->     
    let ty = Ml.ty_in_schema sch in
    let g_tmp = fresh (Liq.mk_sort_env env) dinfos ty in
    let new_c = [WF (env, g_tmp)] in
    let () = log_tmp "auxi" g_tmp in
    let () = log_cons "" new_c in
    let g_sch = Liq.mk_mono_schmea g_tmp in
    (TaSyn.PAuxi (g, g_sch),
     Liq.TLet (Liq.env_empty, g_tmp),
     new_c)
    


and cons_gen_b dinfos env b req_ty =
  match b with
  |TaSyn.PIf (e1, t2, t3) ->
    (* logging *)
    let () = log_place "if judgement" (TaSyntax.PE e1) in 
    let (e1', (Liq.TLet (c_env1, tmp1)), c1) = cons_gen_e dinfos env e1 in
    (match tmp1 with
     |Liq.TScalar (Liq.TBool, phi) ->
       let phi_true =           (* [true/_v]phi *)
         Formula.substitution
           (M.singleton Id.valueVar_id (Formula.Bool true))
           phi
       in
       let phi_false =           (* [false/_v]phi *)
         Formula.substitution
           (M.singleton Id.valueVar_id (Formula.Bool false))
           phi
       in       
       let env_true = Liq.env_add_F (Liq.env_append c_env1 env) phi_true in
       let env_false = Liq.env_add_F (Liq.env_append c_env1 env) phi_false in
       (* logging *)
       let () = log_place "if true" t2 in 
       let (t2', c2) = cons_gen dinfos env_true t2 req_ty in
       (* logging *)
       let () = log_place "if false" t3 in 
       let (t3', c3) = cons_gen dinfos env_false t3 req_ty in
       (TaSyn.PIf (e1', t2', t3'),
        c1@c2@c3)
     | _ -> assert false

    )
  |TaSyn.PMatch (e1, case_list) ->
    (Printf.printf "match temp:\n%s\n" (Liq.t2string req_ty));
    (* logging *)
    let () = log_place "match scru" (TaSyntax.PE e1) in 
    let (e1', e1_tmp, c1) = cons_gen_e dinfos env e1 in
    let case_list', case_list_c = List.map (cons_gen_case dinfos env req_ty e1_tmp) case_list
                                  |> List.split
    in
    (TaSyn.PMatch (e1', case_list'),
     (List.concat case_list_c)@c1)
    

and cons_gen_case dinfos env req_ty e_tmp  {TaSyn.constructor= con;
                                    TaSyn.argNames = x_sch_list;
                                    TaSyn.body = t} =
  match e_tmp with
  |Liq.TLet (c_env1, (Liq.TScalar (Liq.TData (i, tys, pas), phi))) ->
    (* case固有の環境を作成 *)
    (* logging *)
    let () = log_place (Printf.sprintf "case:%s" con) t in
    let xs = List.map fst x_sch_list in
    let con_sch = (try Liq.env_find env con with _ -> assert false) in
    let con_ty = Liq.instantiate_implicit con_sch tys pas in
    let con_ty' = Liq.t_alpha_convert con_ty xs in
    let x_t_list, phi' = constructor_shape con_ty' in
    let z = Id.genid "z" in
    let z_sort = (match Liq.b2sort (Liq.TData (i, tys, pas)) with Some s ->s
                                                                 |_ -> assert false)
    in
    let z_var = Formula.Var (z_sort, z) in
    (* arg_env = x1:t1...,[z\_v]phi' *)
    let arg_env = Liq.env_add_F
                    (Liq.env_add_list  Liq.env_empty  x_t_list)
                    (Formula.substitution
                       (M.singleton Id.valueVar_id z_var) phi')
    in
    let env' = Liq.env_add_F
                 (Liq.env_append arg_env
                                 (Liq.env_append c_env1 env))
                 (Formula.substitution
                    (M.singleton Id.valueVar_id z_var) phi)
    in
    
    let (t', c_t) = cons_gen dinfos env' t req_ty in
    let x_sch_list' = List.map (fun (x,ty) -> (x, Liq.mk_mono_schmea ty)) x_t_list in
    {TaSyn.constructor = con;
     TaSyn.argNames = x_sch_list';
     TaSyn.body = t'},
      c_t
  | _ -> assert false

and cons_gen_f dinfos env f req_ty =
  (* let tmp_in = fresh dinfos (Ml.ty_in_schema ty_x) in *)
  (* let env' =  (Liq.env_add env (x, tmp_in)) in *)
  (* let (tmp_t, c_t) = cons_gen dinfos env' t in *)
  (* (Liq.TFun ((x, tmp_in), tmp_t), *)
  (*  (WF (env, tmp_in))::c_t) *)
  match f with
  |(TaSyn.PFun ((x, x_sch), t)) ->
    (match req_ty with
     |Liq.TFun ((x', req_ty_in), req_ty_out) ->
       (match Liq.type2sort req_ty_in with
        |None ->                   (* x' and x do not occur in req_ty_out  *)
          let env' =  (Liq.env_add env (x, req_ty_in)) in
          let (t', c_t) = cons_gen dinfos env' t req_ty_out in
          (TaSyn.PFun ((x, Liq.mk_mono_schmea req_ty_in), t'),
            c_t)
        |Some x_sort -> 
          (* let x_var = Formula.Var (x_sort, x) in *)
          (* let x'_var = Formula.Var (x_sort, x') in *)

          let env' =  (Liq.env_add env (x', req_ty_in)) in
          (* adjust argument variable to require type *)
          let replaced_t = TaSyn.replace (M.singleton x x') t in (* [x->x'] *)
          (* let x2x'_sita = M.singleton  x x'_var in *)
          (* let x'2x_sita = M.singleton  x' x_var in *)
          (* let req_ty_out' = (Liq.substitute_F x'2x_sita req_ty_out) in *)
          (* [x' -> x]req_ty_out *)
          let (t', c_t) = cons_gen dinfos env' replaced_t req_ty_out in
          (TaSyn.PFun ((x', Liq.mk_mono_schmea req_ty_in), t'),
           c_t)
       )
     |_ -> assert false)
   
  |TaSyn.PFix ((fname, sch_f, inst_schs), f_body) ->
    let mlty_of_fix = Ml.ta_infer_f (Ml.shape_env env) f in
    assert (mlty_of_fix = Ml.shape req_ty);
    let var_in_inst_schs = List.map (function Ml.MLVar i -> i|_ -> assert false)
                                    (List.filter (function Ml.MLVar _ -> true |_->false)
                                                 (List.map Ml.ty_in_schema inst_schs))
    in

    (* let bvs = Liq.free_tvar req_ty in *)
    (* let bvs_in_anno =  Ml.param_in_schema sch_f in *)
    (*  応急処置*)
    (* (assert ((List.length bvs_in_anno) = (List.length bvs))); (\*  *\) *)
    let req_sch = (var_in_inst_schs, [], req_ty) in
    let f_body',c =  cons_gen_f dinfos (Liq.env_add_schema env (fname, req_sch)) f_body req_ty in
    (TaSyn.PFix ((fname, req_sch, []), f_body'), (* このannotationは適当 *)
     c)
    
    
    

let cons_gen_infer dinfos env t  =
  let tmp = mk_tmp dinfos env t in
  let new_c =  (WF (env, tmp)) in
  let () = log_tmp "toplevel" tmp in
  let () = log_cons "" [new_c] in
  let (t', cs) = cons_gen dinfos env t tmp in
  let cs = new_c::cs in
  (t', tmp, cs)
  
