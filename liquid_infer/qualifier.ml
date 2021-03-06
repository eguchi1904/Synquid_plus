open Extensions
type t = (Id.t list) * Formula.t
(*
     * < 1: (x, x < 1) 
*)

let formula_to_qualifier (e:Formula.t) = ([], e)

let mk_qualifier bvs e = (bvs, e)
                       

let substitution (subst:Formula.subst) ((bvs, e):t) = (bvs, Formula.substitution subst e)


(* 
return well formed assignments to variable in qualifier

input
----------------------------------------
senv: environment of well formedness 
q_var_sort: (variable in qualifier * its sort) list

output
----------------------------------------
list of all possible (sita_var, sita_sort)

 *)

(* AnyS i -> UnknownS i *)
let any2unknown sort  =
  let any2unknown_list = List.map (fun i -> (i, Formula.UnknownS i))
                                  (S.elements (Formula.var_in_sort sort))
  in
  let subst = M.add_list any2unknown_list M.empty in
  Formula.sort_subst subst sort


  
  

let rec gen_sita_q_list (senv: (Id.t * Formula.sort) list)
                        (q_var_sort: ((Id.t * Formula.sort) list))
                        sita_var     (* var subst for q_var_sort *)
                        sita_sort   (* sort subst for q_var_sort *)
  =
  match q_var_sort with
  |(v1, v1_sort)::left ->
    let v1_sort = Formula.sort_subst sita_sort v1_sort in
    (* convert  AnyS i in v1_sort which isnt include in sita_sort
       AnyS i-> UnknownS i 
     *)
    let fv_v1_sort = Formula.var_in_sort v1_sort in
    let yet_instantiate_var =
      S.elements
        (S.filter (fun v -> M.mem v sita_sort) fv_v1_sort)
    in
    let any2unknown_list = List.map (fun i -> (i, Formula.UnknownS i)) yet_instantiate_var in
    let any2unknown = M.add_list any2unknown_list M.empty in
    let v1_sort = Formula.sort_subst any2unknown v1_sort in
    let sita_var_sita_sort_candi =
      List.map
        (fun (x, x_sort) ->
          try
            let sita_sort_x_v1 = Formula.unify_sort [(v1_sort, x_sort)] M.empty in
            let sita_var' = M.add v1 (Formula.Var (x_sort, x)) sita_var  in
            let sita_sort' = M.union (fun _ -> assert false) sita_sort_x_v1 sita_sort in
            gen_sita_q_list senv left sita_var' sita_sort'
          with
            Formula.Unify_Err -> [])
        senv
    in
    List.concat sita_var_sita_sort_candi

  |[] ->
    let fv_in_sita_var =
      M.fold
        (fun x x_p acc -> S.union (Formula.fv_include_v x_p) acc)
        sita_var
        S.empty
    in
    if (S.mem Id.valueVar_id fv_in_sita_var)||
         (S.exists (Id.is_pa_arg) fv_in_sita_var)
    then
      [(sita_var, sita_sort)]
    else 
      []

    
exception Unify_under_senv_err of string
let unify_under_senv (senv: (Id.t * Formula.sort) list) (var_sort: (Id.t * Formula.sort) list) =
  try
    let consts =
      List.map (fun (x, sort) ->(sort, List.assoc x senv)) var_sort
    in
    Formula.unify_sort consts M.empty
  with
  |Not_found -> raise (Unify_under_senv_err "illformed")
  |Formula.Unify_Err -> raise (Unify_under_senv_err "cannot unify")

 
                          
    
                              
let gen_p_candidate const_var_sita (senv: (Id.t * Formula.sort) list) ((bvs, e):t) =
try
  (* check the well formuedness about unbounded var and unify its sort *)
  let q_var_sort =  Formula.fv_sort_include_v e in
  let bounded_var_sort, unbounded_var_sort =
    List.partition (fun (x, sort) -> List.mem x bvs) q_var_sort
  in
  let unbounded_var_sort' = List.map (fun (x, sort) -> (x, any2unknown sort)) unbounded_var_sort in
  (* unify_under_senv; this may raise exception *)
  let sortvar_in_unbounded_var_sita = unify_under_senv senv unbounded_var_sort' in
  let unbounded_var_sita_list =
    List.map
      (fun (x, sort') ->
        let  x_sort = Formula.sort_subst sortvar_in_unbounded_var_sita sort' in
        (x, Formula.Var (x_sort, x)))
      unbounded_var_sort'
  in
  let unbounded_var_sita = M.add_list unbounded_var_sita_list M.empty in
  let unbounded_var_sort_sita_list = M.bindings sortvar_in_unbounded_var_sita in (* debug *)
  (* enumerate possible instantiation of bounded variable  *)
  let sita_var_sita_sort_list = gen_sita_q_list
                                  senv
                                  bounded_var_sort
                                  unbounded_var_sita
                              sortvar_in_unbounded_var_sita
  in
  let p_candi = 
  List.map
    (fun (sita_var, sita_sort) ->
      Formula.substitution sita_var
                           (Formula.sort_subst2formula sita_sort e))
    sita_var_sita_sort_list
  in
  let p_candi = List.map (Formula.substitution const_var_sita) p_candi in
  let p_candi = List.uniq_f Formula_eq.f p_candi in
  p_candi
with
  Unify_under_senv_err _ -> []


let rec refine_qualifiers const_var_sita qs =
  let qs = List.map (substitution const_var_sita) qs in
  List.uniq_f (fun (_, e1) (_, e2) -> Formula_eq.f e1 e2) qs
