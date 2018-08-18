open Type
open Extensions
   
let rec fvar_alpha_convert (env: Formula.t M.t) (gen_id: (Id.t * Type.t) ->  Id.t)  = function
  |TScalar (b, phi) -> TScalar (fvar_alpha_convert_basetype env gen_id b,
                                Formula.substitution env phi)
  |TFun ((x, ty1), ty2) ->
    let x' = gen_id (x, ty1) in
    let dummyS = Formula.BoolS in
    let env2 = M.add x (Formula.Var (dummyS, x')) env in
    TFun ((x', fvar_alpha_convert env gen_id ty1),
          fvar_alpha_convert env2  gen_id  ty2)
  |TBot -> TBot

and fvar_alpha_convert_basetype env gen_id  = function
  |TBool|TInt|TAny _ as b -> b
  |TData (i, tys, pas) ->
    TData (i, List.map (fvar_alpha_convert env gen_id) tys,
           List.map (Formula.substitution_to_pa env) pas)
  |TVar _ -> assert false


let fvar_alpha_convert_sch  env (gen_id: (Id.t * Type.t) ->  Id.t)   ((ts,ps,ty):schema) =
  (ts, ps, fvar_alpha_convert env gen_id ty)

let rec tvar_alpha_convert (gen_id: Id.t ->  Id.t)  ty =
  let a_list = free_tvar ty in
  let sita = List.fold_left
               (fun acc a ->
                 let new_a = gen_id a in
                 M.add a (id2TAny new_a) acc)
               M.empty
               a_list
  in
  substitute_T sita ty

let rec tvar_alpha_convert_sch (gen_id: Id.t ->  Id.t)   ((ts,ps,ty):schema) =
  let fv_ty = free_tvar ty in
  let a_list = List.uniq (ts@fv_ty) in
  let sita_list = List.map (fun  a -> (a, gen_id a)) a_list in
  let sita = List.fold_left
               (fun acc (a, new_a) -> M.add a (id2TAny new_a) acc)
               M.empty
               sita_list
  in
  let new_ty = substitute_T sita ty in
  let new_ts = List.map (fun a -> List.assoc a sita_list) ts in
  (new_ts, ps, new_ty)

let mk_readable_ty ty =
  let tvar_count = ref 0 in
  let fvar_count = ref 0 in
  let fvar_conut_func_ty = ref 0 in
  let gen_tvar_id _ =
    let id = Char.escaped (Char.chr (97 + !tvar_count)) in (* 97 == 'a' in ascii code *)
    (tvar_count := !tvar_count + 1);
    id
  in
  let gen_fvar_id (_, ty) =
    match ty with
    |TFun _ ->
      let id =  Char.escaped (Char.chr (102 + !fvar_conut_func_ty)) in (* 102 == 'f' *)
      (fvar_conut_func_ty := !fvar_conut_func_ty + 1);
      id
    |_ ->
      (fvar_count := !fvar_count + 1);
      Printf.sprintf "x%d" !fvar_count
  in
  fvar_alpha_convert M.empty gen_fvar_id
                     (tvar_alpha_convert gen_tvar_id ty)

let mk_readable_sch (sch:schema) =
  let tvar_count = ref 0 in
  let fvar_count = ref 0 in
    let gen_tvar_id _ =
    let id = Char.escaped (Char.chr (97 + !tvar_count)) in
    (tvar_count := !tvar_count + 1);
    id
  in
  let gen_fvar_id _ =
    (fvar_count := !fvar_count + 1);
    Printf.sprintf "x%d" !fvar_count
  in
  fvar_alpha_convert_sch M.empty gen_fvar_id
                     (tvar_alpha_convert_sch gen_tvar_id sch)
  
