open Extensions
open Qualifier
   
module Liq = Type
module TaSyn = TaSyntax

exception LiqErr of string
(* log file *)
let cons_och = open_out "constraints.log"

let solving_och = open_out "solving.log"
             

(* -------------------------------------------------- *)
(* constraint: well formedness / subtyping  *)
(* -------------------------------------------------- *)    
type cons = |WF of (Liq.env * Liq.t)
            |Sub of (Liq.env * Liq.t * Liq.t )

type simple_cons = |SWF of ((Id.t * Formula.sort) list * Formula.t) 
                   |SSub of (Liq.env * Formula.t * Formula.t)
(* unknown predicate が入ると、envからformulaの抽出の仕方が定まらないので、
simple_consでも、type envを持つ必要がある *)
type inst_simple_cons = |InstSWF of ((Id.t * Formula.sort) list * Formula.t) 
                        |InstSSub of (Formula.t * Formula.t * Formula.t)


let cons2string = function
  |WF (env, ty) -> Printf.sprintf "WF\n %s\n%s\n" (Liq.env2string env) (Liq.t2string ty)
  |Sub (env, ty1, ty2) ->
    Printf.sprintf "Sub\n %s\n%s <: %s\n"
                   (Liq.env2string env) (Liq.t2string ty1)  (Liq.t2string ty2)

let cons2string_human = function
  |WF (env, ty) ->
    let bindings = String.concat "; " (Liq.env_bindings env) in
        Printf.sprintf "WF\n %s\n%s" bindings (Liq.t2string ty)
  |Sub (env, ty1, ty2) ->
    Printf.sprintf "Sub\n%s \n<:\n %s"
                   (Liq.t2string ty1)  (Liq.t2string ty2)

   

let scons2string = function
  |SWF (senv, e1)->
    let senv_str =
      String.concat
        "\n"
        (List.map
           (fun (x, sort) ->
             Printf.sprintf "%s: %s" x (Formula.sort2string sort))
           senv)
    in
    Printf.sprintf "SWF\n--------------------------------------------------\n%s\n--------------------------------------------------\n%s\n"
                   senv_str
                   (Formula.p2string_with_sort e1)
    
  |SSub (env, e1, e2) ->
    Printf.sprintf "--------------------------------------------------\n%s\n--------------------------------------------------\n%s <:%s\n"
                   (Liq.env2string env)
                   (Formula.p2string_with_sort e1)
                   (Formula.p2string_with_sort e2)

 
let inst_scons sita = function
  |SSub (env, e1, e2) ->
    let e1' = Formula.substitution sita e1 in
    let e2' = Formula.substitution sita e2 in    
    let env_formula = Liq.env2formula env (S.union (Formula.fv e1') (Formula.fv e2')) in
    (env_formula, e1, e2)
  |SWF (env, p) -> assert false    
   
 let scons2string_human sita sc=
  match sc with
  |SWF _ -> scons2string  sc
  |SSub (env, e1, e2) ->
    let (env_fomula, e1, e2) = inst_scons sita sc in
    let env_fomula_list = Formula.list_and env_fomula in
    let env_fomula_list_str =
      String.concat ";\n"
                    (List.map Formula.p2string env_fomula_list)
    in
    Printf.sprintf "--------------------------------------------------\n%s\n--------------------------------------------------\n%s <:%s\n"
                   env_fomula_list_str
                   (Formula.p2string e1)
                   (Formula.p2string e2)
    
    
                          
     
let is_valid_simple_cons z3_env = function
  |SSub (env, e1, e2 ) -> (* env/\e => sita*P *)
    let env_formula = Liq.env2formula env (S.union (Formula.fv e1) (Formula.fv e2)) in
   let p = (Formula.Implies ( (Formula.And (env_formula,e1)), e2)) in
   let z3_p,p_s = UseZ3.convert p in
   UseZ3.is_valid z3_p
 |SWF (senv, e) ->
       let x_sort_list = Formula.fv_sort_include_v e in
   (* omit checking if e has a boolean sort *)
   List.for_all (fun x_sort -> List.mem x_sort senv) x_sort_list

let subst_cons sita = function
  |WF (env, ty) -> WF (Liq.env_substitute_F sita env, Liq.substitute_F sita ty)
  |Sub (env, ty1, ty2) ->Sub ((Liq.env_substitute_F sita env, Liq.substitute_F sita ty1,
                               Liq.substitute_F sita ty2))
   

let subst_simple_cons sita = function
  |SSub (env, e1, e2) ->
    SSub (Liq.env_substitute_F sita env,
          Formula.substitution sita e1,
          Formula.substitution sita e2)
  |SWF (senv, e) ->
    SWF (senv, Formula.substitution sita e)
    
   

let unknown_p_in_simple_cons = function
  |SWF (senv, e) -> Formula.extract_unknown_p e
  |SSub (e_env, e1, e2) -> (S.union
                             (Liq.env_extract_unknown_p e_env)
                             (S.union
                                (Formula.extract_unknown_p e1)
                                (Formula.extract_unknown_p e2)))
                             

(* env|-(\x.p1) <:(\y.p2) などからsimple_consを生成 *)
let pa_subtyping_to_simple_cons env (args1, p1) (args2, p2) =
  (* まず、p2の引数をp1に合わせる。 *)
  let rec mk_subst args1 args2 =
    List.fold_left2
      (fun sita2 (i1,s1) (i2,s2) ->
        assert (s1 = s2);
        if i1 = i2 then
          sita2
        else
          assert false
          (* let input = Formula.Var (s1, i1) in *)
          (* let sita2' = M.add i2 input sita2 in *)
          (* sita2' *))
      M.empty
      args1
      args2
  in
  let sita2 =mk_subst args1 args2  in
  let p2' = Formula.substitution sita2 p2 in
  (* let env_f = Liq.env2formula env (S.union (Formula.fv p1) (Formula.fv p2')) in *)
  (SSub (env, p1, p2'))
  
                          
(* spit cons to simple_cons list *)
let rec split_cons (c:cons) = match c with
  |WF (env, Liq.TFun ((x, ty1), ty2) ) ->
    let env2 = Liq.env_add env (x, ty1) in
   (split_cons (WF (env, ty1)))@(split_cons (WF (env2, ty2)))
  |WF (env, Liq.TScalar (base_ty, phi)) ->
    (match Liq.b2sort base_ty with
    |None -> raise (LiqErr "dont know what sort is this")
    |Some b_sort ->
      let senv =(Liq.mk_sort_env env) in
      (match base_ty with
       |Liq.TData (data, tys, pas) ->
         let tys_simple_cons = 
           List.concat (List.map (fun ty -> split_cons (WF (env, ty))) tys)
         in
         let pas_simple_cons =
           List.map (fun (args_sort, p) -> SWF(args_sort@senv, p)) pas
         in
         (SWF ((Id.valueVar_id, b_sort)::senv, phi))::(tys_simple_cons@pas_simple_cons)
       |Liq.TBool|Liq.TInt|Liq.TAny _ ->
         [SWF ((Id.valueVar_id, b_sort)::senv, phi)]
       |Liq.TVar _ -> assert false (* becase TVar will be unused *)))
  |WF (env, Liq.TBot) -> []

  |Sub (env,
        Liq.TFun ((x, ty1_in), ty1_out),
        Liq.TFun ((y, ty2_in), ty2_out)  ) -> (* ty1_in -> ty1_out <: ty2_in -> ty2_out *)
    let simple_cons_in = split_cons (Sub (env, ty2_in, ty1_in)) in
    let env2 = Liq.env_add env (y, ty2_in) in
    let ty1_out' =
      if x = y then
        ty1_out
      else
        let y_sort = (match Liq.type2sort ty2_in with Some s -> s| _ -> assert false) in
        let y_var = Formula.Var (y_sort, y) in
        Liq.substitute_F (M.singleton x y_var) ty1_out in (* [y/x]ty1_out *)
    let simple_cons_out = split_cons (Sub (env2, ty1_out', ty2_out)) in
    simple_cons_in@simple_cons_out
  |Sub (env,
        Liq.TScalar (b1, phi1),
        Liq.TScalar (b2, phi2) ) ->
    (* let phi_env = Liq.env2formula env (S.union (Formula.fv phi1) (Formula.fv phi2)) in *)
    (match b1,b2 with
     |(Liq.TData (data, tys1, pas1)),(Liq.TData (data', tys2, pas2)) when data = data' ->
       let tys_simple_cons =
         List.concat (List.map2 (fun ty1 ty2 -> split_cons (Sub (env, ty1, ty2))) tys1 tys2)
       in
       let pas_simple_cons =
         List.map2 (pa_subtyping_to_simple_cons env) pas1 pas2
       in
       (SSub (env, phi1, phi2))::(tys_simple_cons@pas_simple_cons)
     |(Liq.TBool,Liq.TBool)  |(Liq.TInt,Liq.TInt) ->
       [SSub (env, phi1, phi2)]
     |(Liq.TAny i, Liq.TAny i') when i = i' ->
       [SSub (env, phi1, phi2)]
     |(Liq.TVar _, Liq.TVar _) -> assert false  (* becase TVar will be unused *)

     |(_, _) ->
       (Printf.printf "base type miss match:%s vs %s\n" (Liq.b2string b1) (Liq.b2string b2));
       assert false    (* basetype miss match *)
    )
  |Sub (env, Liq.TBot, _) -> []
  |Sub  (env, ty1, ty2) ->
    (Printf.printf "shape miss match:%s vs %s" (Liq.t2string ty1) (Liq.t2string ty2));
    assert false        (* shape miss match *)
       
       
(* -------------------------------------------------- *)
(* pp *)
(* -------------------------------------------------- *)  

let rec cons_list_to_string cs = match cs with
  |cons::left -> Printf.sprintf "%s\n\n\n%s" (cons2string cons)
                               (cons_list_to_string left)
  |[] -> ""

       
let rec cons_list_to_string_human cs = match cs with
  |cons::left -> Printf.sprintf "%s%s" (cons2string_human cons)
                               (cons_list_to_string_human left)
  |[] -> ""


let rec scons_list_to_string scs = match scs with
  |scons::left ->  Printf.sprintf "%s\n\n\n%s" (scons2string scons)
                                  (scons_list_to_string left)
  |[] -> ""

       
  
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
    |SWF (senv, e1) ->
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

let rec fresh (data_info_map: Data_info.t M.t) t =
  let open Data_info in
  match t with
  |Ml.MLBool -> Liq.TScalar (Liq.TBool, Formula.genUnkownP "k")
  |Ml.MLInt -> Liq.TScalar (Liq.TInt, Formula.genUnkownP "k")
  |Ml.MLData (i, tys) when M.mem i data_info_map ->
    let tys_tmp = List.map (fresh data_info_map) tys in
    let data_info = M.find i data_info_map in
    let pa_shape_list = Data_info.instantiate_pred_param_shape data_info tys_tmp in
    let unknown_pa_list = List.map
                            (fun (s, shape) -> Formula.genUnknownPa_shape shape s)
                            pa_shape_list
    in
    
    Liq.TScalar (Liq.TData (i, tys_tmp, unknown_pa_list), Formula.genUnkownP "k")
  |Ml.MLData (i, _) -> assert false
  |Ml.MLVar x -> Liq.TScalar ((Liq.TAny x), Formula.genUnkownP "k") (* TAny i　型 *)
  |Ml.MLFun (ty1, ty2) ->
    let x = Id.genid "x" in
    Liq.TFun ((x, (fresh data_info_map ty1)), (fresh data_info_map ty2))
      

let mk_tmp dinfos env t =
  let tmp = fresh  dinfos (Ml.ta_infer (Ml.shape_env env) t) in
  tmp

            
let rec cons_gen dinfos env t req_ty =
  match t with
  |TaSyn.PLet ((x, (alist, ty)), t1, t2) when S.mem x (TaSyn.fv t1)-> (* recursive def *)
    let new_tmp_x =  fresh dinfos ty in
    let new_tmp_x_sch = (alist, [], new_tmp_x) in
    let new_c =  [WF (env, new_tmp_x)] in
    (* logging *)
    let () = log_cons "" new_c in
    let () = log_tmp x new_tmp_x in
    (* disable let polimorphism for predicate *)
    let env2 =  (Liq.env_add_schema env (x, new_tmp_x_sch)) in
    let (_, c1) = cons_gen dinfos env2 t1 new_tmp_x in
    (* let env2 =  (Liq.env_add env (x, tmp1)) in *)
    let (_, c2) = cons_gen dinfos env2 t2 req_ty in
    (req_ty, new_c@c1@c2)
 |TaSyn.PLet ((x, (alist, ty)), t1, t2) ->
   let new_tmp_x = fresh dinfos ty in
   let (_, c1) = cons_gen dinfos env t1 new_tmp_x in
    (* disable let polimorphism for predicate *)
   let new_tmp_x_sch = (alist, [], new_tmp_x) in
   let new_c =  [WF (env, new_tmp_x)] in
   (* logging *)
   let () = log_cons "" new_c in
   let () = log_tmp x new_tmp_x in
   
    let env2 =  (Liq.env_add_schema env (x, new_tmp_x_sch )) in
    (* let env2 =  (Liq.env_add env (x, tmp1)) in *)
    let (_, c2) = cons_gen dinfos env2 t2 req_ty in

    (req_ty, new_c@c1@c2)    
  |TaSyn.PE e ->
    let ((Liq.TLet (c_env, tmp_e)), c) = cons_gen_e dinfos env e in
    let new_c = [Sub ((Liq.env_append env c_env), tmp_e, req_ty)] in
    let () = log_cons "" new_c in
    (req_ty, new_c@c )
  |TaSyn.PI b -> cons_gen_b dinfos env b req_ty
  |TaSyn.PF f -> cons_gen_f dinfos env f req_ty
  |TaSyn.PHole -> assert false

and cons_gen_e dinfos env e =

  match e with
  |TaSyn.PAppFo (e1, e2) ->
    (match cons_gen_e dinfos env e1 with
     (* e1 :: x:tmp_in -> tmp_out *)
     |((Liq.TLet (c_env1, (Liq.TFun ((x, tmp_in), tmp_out) ) )), c1) ->
       let open Formula in
       let Liq.TLet (c_env2, tmp2), c2 = cons_gen_e dinfos env e2 in
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
           ((Liq.TLet (c_env, tmp_out')),
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
           ((Liq.TLet (c_env, tmp_out')),
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
          ((Liq.TLet (c_env, tmp_out')),
           new_c@(c1@c2)
          )
        | Liq.TFun _ -> assert false
        | Liq.TBot -> assert false
       )
       
     |((Liq.TLet (_, ty)), _) ->
       (Printf.printf "exspect:function type but got\n%s" (Liq.t2string ty));
       assert false
    )
  |TaSyn.PAppHo (e1, f1)  ->
    let tmp_f1 =  fresh  dinfos (Ml.ta_infer_f (Ml.shape_env env) f1)  in
    let (_, c_f1) = cons_gen_f dinfos env f1 tmp_f1 in
    (match cons_gen_e dinfos env e1 with
     |((Liq.TLet (c_env1, Liq.TFun ((x, tmp_in), tmp_out) )), c_e1) ->
       let new_c =    [(Sub (Liq.env_append env c_env1, tmp_f1, tmp_in));
                       WF (env, tmp_f1)]
       in
       (* logging *)
       let () = log_place "application(higher order)" (TaSyntax.PE e) in 
       let () = log_tmp "appHO arg" tmp_f1 in
       let () = log_cons "" new_c in
       (Liq.TLet (c_env1, tmp_out),
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
          (Liq.TLet (Liq.env_empty, Liq.TScalar (b, (Eq
                                                       (Var (b_sort, Id.valueVar_id),
                                                        Var (b_sort, x))))),
           [])
        |None ->  raise (LiqErr "dont know what sort is this"))
       
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
       let unknown_pa_and_c_pa_list =
         List.map
           (fun (p, (arg_sort, rets)) ->
             let (args, p) = Formula.genUnknownPa_shape (arg_sort, rets) p in
             (* make well formedness constraints *)
             let arg_env= List.map (fun (x, sort) -> (x, Liq.sort2type sort))
                                   args
             in
             let env' = Liq.env_add_list env arg_env in
             let wf_con = WF (env', Liq.TScalar ((Liq.sort2type_base rets), p)) in
             (args, p), wf_con
           )
           plist
       in
       let unknown_pa_list, c_pa_list = List.split unknown_pa_and_c_pa_list in

       (* typeのinstantiate *)
       let tys_tmp = List.map (fresh dinfos) tys in
       let c_tys = List.map (fun ty -> WF (env, ty)) tys_tmp in

       let ty_x' = Liq.instantiate_implicit x_liq_sch tys_tmp unknown_pa_list in
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
       let new_c =  c_pa_list@c_tys in
       let () = log_cons "" new_c in
       (Liq.TLet (Liq.env_empty, ty_x'),new_c))

  |TaSyn.PInnerFun f_in ->
     let tmp_f =  fresh  dinfos (Ml.ta_infer_f (Ml.shape_env env) f_in)  in
     let (_, c_f) = cons_gen_f dinfos env f_in tmp_f in
     let new_c = [WF (env, tmp_f)] in
  (* logging *)
     let () = log_place "inner function" (TaSyntax.PF f_in) in
     let () = log_tmp "inner function" tmp_f in
     let () = log_cons "" new_c in
     (Liq.TLet (Liq.env_empty, tmp_f), new_c@c_f)
  |TaSyn.PAuxi _ -> assert false

and cons_gen_b dinfos env b req_ty =
  match b with
  |TaSyn.PIf (e1, t2, t3) ->
    (* logging *)
    let () = log_place "if judgement" (TaSyntax.PE e1) in 
    let ((Liq.TLet (c_env1, tmp1)), c1) = cons_gen_e dinfos env e1 in
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
       let (_, c2) = cons_gen dinfos env_true t2 req_ty in
       (* logging *)
       let () = log_place "if false" t3 in 
       let (_, c3) = cons_gen dinfos env_false t3 req_ty in
       (req_ty,
        c1@c2@c3)
     | _ -> assert false

    )
  |TaSyn.PMatch (e1, case_list) ->
    (Printf.printf "match temp:\n%s\n" (Liq.t2string req_ty));
    (* logging *)
    let () = log_place "match scru" (TaSyntax.PE e1) in 
    let (e1_tmp, c1) = cons_gen_e dinfos env e1 in
    let case_list_c = List.map (cons_gen_case dinfos env req_ty e1_tmp) case_list in
    (req_ty,
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
    
    let (tmp_t, c_t) = cons_gen dinfos env' t req_ty in
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
          let (_, c_t) = cons_gen dinfos env' t req_ty_out in
          (req_ty, c_t)
        |Some x_sort -> 
          (* let x_var = Formula.Var (x_sort, x) in *)
          (* let x'_var = Formula.Var (x_sort, x') in *)

          let env' =  (Liq.env_add env (x', req_ty_in)) in
          (* adjust argument variable to require type *)
          let t' = TaSyn.replace (M.singleton x x') t in (* [x->x'] *)
          (* let x2x'_sita = M.singleton  x x'_var in *)
          (* let x'2x_sita = M.singleton  x' x_var in *)
          (* let req_ty_out' = (Liq.substitute_F x'2x_sita req_ty_out) in *)
          (* [x' -> x]req_ty_out *)
          let (_, c_t) = cons_gen dinfos env' t' req_ty_out in
          (req_ty,((* List.map (subst_cons x2x'_sita) *) c_t))
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
    cons_gen_f dinfos (Liq.env_add_schema env (fname, req_sch)) f_body req_ty

      
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
                     |SWF (senv, Formula.Unknown (sort_sita, sita, k)) ->
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
  |SWF (senv, Formula.Unknown (sort_sita_i, sita_i, i)) ->
    let qs = M.find i pcandi in
    let qs' = List.filter
                (fun q -> let q' = (Formula.sort_subst2formula sort_sita_i (Formula.substitution sita_i q)) in
                          is_valid_simple_cons z3_env (SWF (senv, q')))
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


(* -------------------------------------------------- *)
(* main *)
(* -------------------------------------------------- *)  
  
  
    
let liqInfer z3_env dinfos qualifiers env ta_t =
  let st_infer = Sys.time () in
  (print_string (TaSyn.syn2string Ml.string_of_sch ta_t));
  let tmp = mk_tmp dinfos env ta_t in
  let new_c =  (WF (env, tmp)) in
  let () = log_tmp "toplevel" tmp in
  let () = log_cons "" [new_c] in
  let (_, cs) = cons_gen dinfos env ta_t tmp in
  let cs = new_c::cs in
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs) in
  let () = (Printf.printf "cs_length:%d \n" (List.length cs)) in
  let () =  (Printf.printf "simple_cs_length:%d \n" (List.length simple_cs)) in
  (* (print_string (scons_list_to_string simple_cs)); *)
  let const_var_sita = Liq.mk_subst_for_const_var env in
  let toplevel_ks = Liq.extract_unknown_p tmp in
  let st = Sys.time () in
  let p_candi = init_p_assignment const_var_sita qualifiers simple_cs toplevel_ks in
  let ed = Sys.time () in
  (Printf.printf "\n\nend_init_p_candi:%f\n\n" (ed -. st ));
    (* logging *)
  let () = log_assingment "initial assignment" p_candi in
  
  let p_candi_debug = M.bindings p_candi in
  let p_assign = solve z3_env simple_cs p_candi in
  (* logging *)
  let () = log_assingment "solved assignment" p_assign in
  let () = log_simple_cons "solved constraint" simple_cs in
  let sita = M.map (fun tlist -> Formula.and_list tlist) p_assign in
  let ed_infer = Sys.time () in
  let () = (Printf.printf "\n\nLiq_INfer:%f\n\n" (ed_infer -. st_infer )) in
  Liq.substitute_F sita tmp
  
  
let liqCheck z3_env dinfos qualifiers env ta_t req_ty =
  let st_infer = Sys.time () in
  (print_string (TaSyn.syn2string Ml.string_of_sch ta_t));
  let (_, cs) = cons_gen dinfos env ta_t req_ty in
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs) in
  let () = (Printf.printf "cs_length:%d \n" (List.length cs)) in
  let () =  (Printf.printf "simple_cs_length:%d \n" (List.length simple_cs)) in
  (* (print_string (scons_list_to_string simple_cs)); *)
  let const_var_sita = Liq.mk_subst_for_const_var env in
  let st = Sys.time () in
  let p_candi = init_p_assignment const_var_sita qualifiers simple_cs S.empty in
  let ed = Sys.time () in
  (Printf.printf "\n\nend_init_p_candi:%f\n\n" (ed -. st ));
  (* logging *)
  let () = log_assingment "initial assignment" p_candi in
    let p_candi_debug = M.bindings p_candi in
  try
    let p_assign = solve z3_env simple_cs p_candi in
    (* logging *)
    let () = log_assingment "solved assignment" p_assign in
    let () = log_simple_cons "solved constraint" simple_cs in
    let sita = M.map (fun tlist -> Formula.and_list tlist) p_assign in
    let ed_infer = Sys.time () in
    let () = (Printf.printf "\n\nLiq_check:%f\n\n" (ed_infer -. st_infer )) in
    true
  with
    SolvingErr mes ->
    let ed_infer = Sys.time () in
    let () = (Printf.printf "\n\n%s Liq_check:%f\n\n" mes (ed_infer -. st_infer )) in
    raise (SolvingErr mes)


let f  z3_env dinfos qualifiers env t =
  let inlined_t = Syntax.inline_rec_fun M.empty t in
  let (ta_t, ml_ty) = Ml.infer (Ml.shape_env env) inlined_t in
  liqInfer z3_env dinfos qualifiers env ta_t
  

let f_check z3_env dinfos qualifiers env t (_,_,req_ty)=
  let inlined_t = Syntax.inline_rec_fun M.empty t in
  (* let t = Syntax.alpha M.empty t in *)
  let ta_t = Ml.check (Ml.shape_env env) inlined_t (Ml.shape req_ty) in
  (* req_ty を、ml_tyに合わせる必要があるな *)
  (* それか要求を通せる何か、これは辛いな。 *)
  liqCheck z3_env dinfos qualifiers env ta_t req_ty
(* -------------------------------------------------- *)
(* inference of E-term *)
(* -------------------------------------------------- *)
  
let liqInferEterm z3_env dinfos qualifiers env ta_e =
  (* (print_string (TaSyn.syn2string Ml.string_of_sch ta_t)); *)
  let (contextual_tmp, cs) = cons_gen_e dinfos env ta_e in
  (* (Printf.printf "\ntmp: %s\n" (Liq.t2string tmp)); *)
  (* (print_string (cons_list_to_string cs)); *)
  let simple_cs = List.concat (List.map split_cons cs) in
  (* (print_string (scons_list_to_string simple_cs)); *)
  let const_var_sita = Liq.mk_subst_for_const_var env in
  let p_candi = init_p_assignment const_var_sita qualifiers simple_cs S.empty in
  
  let p_candi_debug = M.bindings p_candi in
  let p_assign = solve z3_env simple_cs p_candi in
  let sita = M.map (fun tlist -> Formula.and_list tlist) p_assign in
  match contextual_tmp with
  |Liq.TLet (c_env, ty) ->
    Liq.TLet ((Liq.env_substitute_F sita c_env), Liq.substitute_F sita ty)



  
let fEterm  z3_env dinfos qualifiers env e =
  match Ml.infer (Ml.shape_env env) (Syntax.PE e) with
  |(TaSyn.PE ta_e), ml_ty ->
    liqInferEterm z3_env dinfos qualifiers env ta_e
  | _ -> assert false

