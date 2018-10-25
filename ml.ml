(* -------------------------------------------------- *)
(* ML type inference *)
(* -------------------------------------------------- *)
open Extensions                 (* listモジュールの拡張など *)

exception ML_Inf_Err of string
   
type t =
  |MLBool|MLInt
  |MLData of Id.t * (t list) 
  |MLVar of Id.t
  |MLFun of t * t

module Syn = Syntax
module TaSyn = TaSyntax

             
let rec fv t = match t with
  |MLVar id -> [id]
  |MLData (i, tys) -> List.uniq (List.concat (List.map fv tys))
  |MLBool|MLInt -> []
  |MLFun (t1, t2) -> List.uniq ((fv t1)@(fv t2))

let rec split_function_type t = match t with
  |MLFun (ty1, ty2) ->
    let (arg_tys, ret_ty) = split_function_type ty2 in
    (ty1::arg_tys, ret_ty)
  |MLVar _ |MLData _ |MLBool |MLInt   as ty -> ([],ty)

let rec shape t = match t with
  |Type.TScalar (b, _) -> shape_base b
  |Type.TFun ((_, ty1),ty2) -> MLFun ((shape ty1), (shape ty2))
  |Type.TBot -> assert false

and shape_base b = match b with
  |Type.TBool -> MLBool
  |Type.TInt -> MLInt
  |Type.TData (i, tys, pas) -> MLData (i, (List.map shape tys))
  |Type.TVar (_,x) -> MLVar x
  |Type.TAny x -> MLVar x

let rec string_of_t t :string= let open Printf in
  match t with
  |MLBool -> "bool"|MLInt -> "int"
  |MLVar x -> x
  |MLData (i, tys) ->
    String.concat " " (i::(List.map string_of_t tys))
   
  |MLFun (ty1, ty2) ->
    sprintf "(%s -> %s)" (string_of_t ty1) (string_of_t ty2)

exception T2SORT
let rec t2sort t = match t with
  |MLBool -> Formula.BoolS
  |MLInt -> Formula.IntS
  |MLVar i -> Formula.AnyS i
  |MLData (i, tys) -> Formula.DataS (i, (List.map t2sort tys))
  |MLFun _ -> raise T2SORT
                
(* -------------------------------------------------- *)
(* schema *)
(* -------------------------------------------------- *)
type schema =  (Id.t list) *  t

let ty_of_schema (ty:t) = ([], ty)

let ty_in_schema ((bvs, ty):schema) = ty

let param_in_schema ((bvs, ty)) = bvs

let shape_sch ((bvs, pas, ty):Type.schema) =
  (bvs, shape ty)

let string_of_sch ((bvs,ty):schema) =
  if bvs = [] then
    string_of_t ty
  else
    Printf.sprintf "(%s).%s"
                   (String.concat "," bvs)
                   (string_of_t ty)
  
let generalize fv_list t =  (fv_list, t)

let rec instantiate' table ty = match ty with
  |MLVar x when List.mem_assoc x table -> MLVar (List.assoc x table)
  |MLVar x -> MLVar x
  |MLData (i, tys) -> MLData (i, List.map (instantiate' table) tys)
  |MLBool -> MLBool
  |MLInt -> MLInt
  |MLFun (ty1, ty2) -> MLFun (instantiate' table ty1, instantiate' table ty2)
                          
let instantiate ((bvs, ty):schema) =
  let betas:Id.t list = List.map Id.genid bvs in
  let new_ty = instantiate' (List.combine bvs betas) ty in
  (betas, new_ty)


  

let fv_schema ((bvs, ty):schema) = List.diff (fv ty) bvs

let access_type_in_schema (f:t-> t) ((bvs, ty):schema) = (bvs, (f ty))

(*--------------------------------------------------*)
(* environment *)
(*--------------------------------------------------*)
type 'a env = (Id.t * 'a) list

let rec shape_env ((table, _):Type.env) : schema env= 
  List.map (fun (x, sch) -> (x, shape_sch sch)) table
  

let empty_env = []
              
let add_env x t env = (x, t)::env

let add_list_env xs env = xs@env

let find_env x (env:'a env) = List.assoc x env

let mem_env x env = List.mem_assoc x env

let foldl_env (f:'a -> (Id.t* 'b) -> 'a) (seed:'a) (env:'b env)=   List.fold_left f seed env

let access_data_in_env (f:'a -> 'a) (env:'a env) =
  foldl_env (fun acc (x, sch) -> acc@[(x, f sch)] )  empty_env env
    
let rec access_data_in_env (f:'a -> 'a) (env: 'a env) = match env with
  |(x, sch)::lest -> (x, f sch)::(access_data_in_env f lest)
  | [] -> []

                   
let rec  fv_env env = match env with
  |(x, sch)::lest -> (fv_schema sch)@(fv_env lest)
  |[] -> []


  
  

(* -------------------------------------------------- *)
(* substitution *)
(* -------------------------------------------------- *)
type 'a subst = 'a M.t              (* 肩変数のsubstitution *)

let subst_empty = M.empty

let subst_singleton = M.singleton
              
let rec subst_ty sita ty = match ty with
  |MLVar x when M.mem x sita -> M.find x sita
  |MLVar x -> MLVar x
  |MLData (i, tys) -> MLData (i, List.map (subst_ty sita) tys)
  |MLBool -> MLBool
  |MLInt -> MLInt
  |MLFun (ty1, ty2) -> MLFun ((subst_ty sita ty1), (subst_ty sita ty2))

let subst_sch sita ((bvs, ty):schema) =
  let sita' = M.delete_list sita bvs in
  (bvs, (subst_ty sita' ty))

let subst_env sita env =  access_data_in_env (subst_sch sita) env

let rec subst_cons sita c = match c with
  |(ty1, ty2)::left -> (subst_ty sita ty1, subst_ty sita  ty2)::(subst_cons sita left)
  |[] -> []

let subst_tasyn (sita:t subst) =  TaSyn.access_annotation_t (subst_sch sita)

let subst_tasyn_e (sita:t subst) =  TaSyn.access_annotation_e (subst_sch sita)
                                  
let subst_tasyn_b (sita:t subst) =  TaSyn.access_annotation_b (subst_sch sita)

let subst_tasyn_f (sita:t subst) =  TaSyn.access_annotation_f (subst_sch sita)

let subst_compose (sita1: t subst) (sita2: t subst) = (* \forall t. composed_sita t = sita1(sita2 t) *)
  M.union (fun i t1 t2 -> Some t2)
          sita1
          (M.mapi (fun i t2 -> subst_ty sita1 t2) sita2)

  
let instantiate_implicit tys ((bvs, ty):schema) = 
  if (List.length tys) <> (List.length bvs) then
    raise (ML_Inf_Err "instatiate implicit err")
  else
    let sita = M.add_list2 bvs tys M.empty in
    subst_ty sita ty
      
(* -------------------------------------------------- *)
(* ML type infer *)
(* -------------------------------------------------- *)
                      
           


let rec unify c sita = match c with
  |[] -> sita
  |(MLBool, MLBool)::left|(MLInt, MLInt)::left -> unify left sita
  |(MLVar a, MLVar b)::left when a = b -> unify left sita
  |(MLVar a, ty2)::left when (not (List.mem a (fv ty2))) ->
    let new_left = subst_cons (subst_singleton a ty2) left in
    let new_sita = subst_compose (subst_singleton a ty2) sita in
    unify new_left new_sita
  |(ty2, MLVar a)::left when (not (List.mem a (fv ty2))) ->
    let new_left = subst_cons (subst_singleton a ty2) left in
    let new_sita = subst_compose (subst_singleton a ty2) sita in
    unify new_left new_sita
  |(ty2, MLVar a)::left  ->
    let mess = Printf.sprintf "occurrences err:%s vs %s" (string_of_t ty2) a in
    raise (ML_Inf_Err mess)
  |( MLVar a, ty2)::left ->
    let mess = Printf.sprintf "occurrences err:%s vs %s" (string_of_t ty2) a in
    raise (ML_Inf_Err mess)
  |( (MLFun (ty1_in, ty1_out)), (MLFun (ty2_in, ty2_out)))::left ->
    unify ((ty1_in, ty2_in)::(ty1_out, ty2_out)::left) sita
  |(MLData (i, tys1), MLData (i', tys2))::left when i = i' ->
    if List.length tys1 <> List.length tys2 then
      raise (ML_Inf_Err (Printf.sprintf "data type %s's parameters unmatch" i))
    else
      unify ((List.combine tys1 tys2)@left) sita
  |( ty1, ty2)::left ->
    let mess = Printf.sprintf "infer err:%s vs %s" (string_of_t ty1) (string_of_t ty2) in
    raise (ML_Inf_Err mess)

let unify2 ty1 ty2 = unify [(ty1, ty2)] subst_empty

let rec_def x t =  (Syntax.PLet (x,t, Syntax.PE (Syntax.PSymbol x)))
   
let rec  infer_t env e = match e with
  |Syn.PLet (x, t1, t2) ->
    let alpha = MLVar (Id.genid "alpha") in (* for recursive definition*)
    let (ta_t1, ty1, c1) = infer_t (add_env x (ty_of_schema alpha) env) t1 in
    (* unification *)
    let sita1 = unify ((alpha, ty1)::c1) subst_empty in
    let ty1'   = subst_ty    sita1 ty1   in
    let env'   = subst_env   sita1 env   in
    let ta_t1' = subst_tasyn sita1 ta_t1 in (*redundance ?  *)
    (* derive shcema of t1 *)
    let fv_ty1 = List.diff (fv ty1') (fv_env env' ) in
    let sch1 =  generalize fv_ty1 ty1' in
    (* insert explicit instantiation for recursive function.
       In ml polymorphism, recursive functions are always instantiated by
       its polymorphic type parameter (not by concrete type such as Int or Bool )
     *)
    let fv_ty1_var = List.map (fun beta -> ty_of_schema (MLVar beta)) fv_ty1 in
    let instantiate_x = TaSyn.PSymbol (x, fv_ty1_var) in
    let ta_t1' = TaSyn.substitute x  instantiate_x ta_t1' in
    (* infer t2 *)
    let env2 =  add_env x sch1 env' in
    let (ta_t2, ty2, c2) = infer_t env2 t2 in
    ((TaSyn.PLet ((x, sch1), ta_t1', ta_t2)), ty2, ((alpha, ty1)::c1@c2))
    
  |Syn.PE e -> let (ta_e, ty, c) = infer_e env e in
               (TaSyn.PE ta_e, ty, c)

  |Syn.PI b -> let (ta_b, ty, c) = infer_b env b in
               (TaSyn.PI ta_b, ty, c)

  (* |Syn.PF (Syn.PFix (id, f)) -> infer_t env (rec_def id (Syn.PF f)) *)
                              
  |Syn.PF f -> let (ta_f, ty, c) = infer_f env f in
               (TaSyn.PF ta_f, ty, c)

  |Syn.PHole -> raise (ML_Inf_Err "encounter program hole")

and infer_e env e = match e with
  |Syn.PSymbol x ->
    (try let  sch = find_env x env in
         let (betas, new_ty) = instantiate sch in
         let instans_type_list = List.map (fun i -> ty_of_schema (MLVar i)) betas in
         (TaSyn.PSymbol (x, instans_type_list), new_ty, [])
     with
       Not_found -> raise (ML_Inf_Err (Printf.sprintf "%s is not in scope" x))
    )
  |Syn.PAuxi _ -> raise (ML_Inf_Err "encounter unknown auxiliary function")
  |Syn.PAppFo (e1, e2) ->
    let (ta_e1, ty1, c1) = infer_e env e1 in
    let (ta_e2, ty2, c2) = infer_e env e2 in
    let alpha = MLVar (Id.genid "'a") in
    let c3 = (ty1, MLFun (ty2, alpha))::c1@c2  in
    ( TaSyn.PAppFo (ta_e1, ta_e2),
      alpha,
      c3
    )
  |Syn.PAppHo (e1, f2) ->
    let (ta_e1, ty1, c1) = infer_e env e1 in
    let (ta_f2, ty2, c2) = infer_f env f2 in
    let alpha = MLVar (Id.genid "'a") in
    let c3 = (ty1, MLFun (ty2, alpha))::c1@c2  in
    ( TaSyn.PAppHo (ta_e1, ta_f2),
      alpha,
      c3
    )


and infer_b env b = match b with
  |Syn.PIf (e1, t2, t3) ->
    
    (* infer e1, t2, t3 *)
    let (ta_e1, ty1, c1) = infer_e env e1 in
    let (ta_t2, ty2, c2) = infer_t env t2 in
    let (ta_t3, ty3, c3) = infer_t env t3 in
    (* unification *)
    (TaSyn.PIf (ta_e1, ta_t2, ta_t3),
     ty3,
     [(ty1, MLBool); (ty2, ty3)]@c1@c2@c3)
     

  |Syn.PMatch (e1, cases) ->
    let (ta_e1, ty1, c1) = infer_e env e1 in
    (match cases with
     |[] -> raise (ML_Inf_Err "empty cases")
     |top_case::left_cases ->
       let (ta_top_case, ty_top_case, c_top_case) = infer_case env ty1 top_case in
       let (ta_cases, ty_cases, c_cases) =
         List.fold_left
           (fun (ta_case_list, ty_preb, c_acc) case ->
             let (ta_case, ty_case, c_case) = infer_case env ty1 case in
             (ta_case::ta_case_list, ty_case, (ty_case, ty_preb)::c_case@c_acc))
           ([ta_top_case], ty_top_case , c_top_case)
           left_cases
       in
       (TaSyn.PMatch (ta_e1, ta_cases), ty_cases, c1@c_cases)
    )

and infer_case env matching_ty {Syn.constructor = cons; Syn.argNames = xs; Syn.body = t1} =
  let sch_cons = find_env cons env in
  let (betas, ty_cons) = instantiate sch_cons in
  let (cons_arg_tys, cons_ret_ty) = split_function_type ty_cons in
  (if ( (List.length cons_arg_tys) <> (List.length xs)) then
     raise (ML_Inf_Err "number of constructor's argument"));
  let ta_xs = List.combine xs (List.map ty_of_schema cons_arg_tys) in
  let (ta_t1, ty1, c1) = infer_t (add_list_env ta_xs env) t1 in
  ({TaSyn.constructor = cons; TaSyn.argNames =  ta_xs; TaSyn.body = ta_t1},
   ty1,
   (cons_ret_ty, matching_ty)::c1)

  
and infer_f env f = match f with
  |Syn.PFun (x, t1) ->
    let alpha = MLVar (Id.genid "a") in
    let (ta_t1, ty_t1, c1) = infer_t (add_env x (ty_of_schema alpha) env) t1 in
    (TaSyn.PFun ((x, (ty_of_schema alpha)), ta_t1),
     MLFun (alpha, ty_t1),
     c1)
  |Syn.PFix (f_name, f_body) ->
    let alpha = MLVar (Id.genid "alpha") in (* for recursive definition*)
    let alpha_sch = ty_of_schema alpha in
    let (ta_f, ty_f, c) = infer_f (add_env f_name  alpha_sch env) f_body  in
    
    let sita = unify ((alpha, ty_f)::c) subst_empty in
    let ty_f' = subst_ty sita ty_f in
    let env' = subst_env sita env in
    let fv_ty_f = List.diff (fv ty_f') (fv_env env' ) in
    let sch_f =  generalize fv_ty_f ty_f' in
    (* treat f_name as polimorphic type in the f_body *)
    let fv_ty1_var = List.map (fun beta -> ty_of_schema (MLVar beta)) fv_ty_f in
    let instantiate_f_name = TaSyn.PSymbol (f_name, fv_ty1_var) in
    let ta_f' = TaSyn.substitute_f f_name  instantiate_f_name ta_f in
    
    (TaSyn.PFix ((f_name, sch_f), ta_f'),
     alpha,
     (alpha, ty_f)::c)


let infer env t =
  let (ta_t, ty_t, c) = infer_t env t in
  let sita = unify c subst_empty in
  (subst_tasyn sita ta_t, subst_ty sita ty_t)

let check env t req_ty =
  let (ta_t, ty) = infer env t in
  let sita = unify [(ty, req_ty)] subst_empty in
  subst_tasyn sita ta_t


(*******************************************)
(* type inference of program with type annotation *)
(*******************************************)  
let rec ta_infer env (t:schema TaSyntax.t) = match t with
  |TaSyn.PLet ((x, sch), t1, t2) -> ta_infer (add_env x sch env) t2
  |TaSyn.PE e -> ta_infer_e env e
  |TaSyn.PI b -> ta_infer_b env b
  |TaSyn.PF f -> ta_infer_f env f
  |TaSyn.PHole -> assert false
and ta_infer_e env e = match e with
  |TaSyn.PSymbol (x, tys) ->
    let sch = find_env x env in
    instantiate_implicit (List.map ty_in_schema tys) sch
  |TaSyn.PAuxi _ -> raise (ML_Inf_Err "encounter auxi")
  |TaSyn.PAppFo (e1, _)| TaSyn.PAppHo (e1, _) ->
    (match ta_infer_e env e1 with
     |MLFun (ty1, ty2) -> ty2
     |_ -> assert false
    )

and ta_infer_b env b = match b with
  |TaSyn.PIf (e1, t2, t3) ->   ta_infer env t2
  |TaSyn.PMatch (e, case_list) ->
    (match case_list with
     |case::_ -> ta_infer_case env case
     | [] -> assert false)

and ta_infer_case env {TaSyn.constructor = _ ; TaSyn.argNames = x_ty_list; TaSyn.body = t } =
  ta_infer (add_list_env x_ty_list env) t

and ta_infer_f env f = match f with
  |TaSyn.PFun ((x, sch), t) ->
    let x_ty = ty_in_schema sch in
    let t_ty = ta_infer (add_env x sch env) t in
    MLFun (x_ty, t_ty)
  |TaSyn.PFix ((f_name, sch), f) -> ty_in_schema sch
                             
                             
                             
  
    
