module Liq = Type
exception Constraint of string           

type cons = |WF of (Liq.env * Liq.t)
            |Sub of (Liq.env * Liq.t * Liq.t)

(* synquidの型systemではunknown predicate が入ると、envからformulaの抽出の仕方が定まらないので、
simple_consでも、type envを持つ必要がある *)
type simple_cons = |SWF of Liq.env * ((Id.t * Formula.sort) list * Formula.t) 
                   |SSub of (Liq.env * Formula.t * Formula.t)
                          

type pure_simple_cons = |PSWF of ((Id.t * Formula.sort) list * Formula.t)
                        |PSSub of (Formula.t * Formula.t * Formula.t)


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
  |SWF (_, (senv, e1))->
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
  |SWF (_, (senv, e)) ->
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
  |SWF (env, (senv, e)) ->
    SWF (env, (senv, Formula.substitution sita e))
    
   
let unknown_p_in_simple_cons = function
  |SWF (_, (senv, e)) -> Formula.extract_unknown_p e
  |SSub (e_env, e1, e2) -> (S.union
                             (Liq.env_extract_unknown_p e_env)
                             (S.union
                                (Formula.extract_unknown_p e1)
                                (Formula.extract_unknown_p e2)))



let positive_negative_unknown_p = function
  |SWF _ -> invalid_arg "constraint.positive_negative_unknown_p: well formedness constraint"
  |SSub (env, e1, e2) ->
    let env_formula_all = Liq.env2formula_all env in
    let phi = Formula.Implies ((Formula.And (env_formula_all, e1)), e2) in
    Formula.positive_negative_unknown_p phi

    
let is_predicate_normal_position = function
  |SWF (env, (senv, e))->
    let env_formula_list = Liq.env2formula_all env |> Formula.list_and in
    let e_list = Formula.list_and e in
    List.for_all
      (fun e -> Formula.is_unknown_p e || S.is_empty (Formula.extract_unknown_p e))
      (env_formula_list@e_list)
  |SSub (env, e1, e2) ->
    let env_formula_list = Liq.env2formula_all env |> Formula.list_and in
    let e1_list = Formula.list_and e1 in
    let e2_list = Formula.list_and e2 in
    List.for_all
      (fun e -> Formula.is_unknown_p e || S.is_empty (Formula.extract_unknown_p e))
      (env_formula_list@e1_list@e2_list)    
    
    

                             

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
let rec split_cons' top_env (c:cons) =
  match c with
  |WF (env, Liq.TFun ((x, ty1), ty2) ) ->
    let env2 = Liq.env_add env (x, ty1) in
    (split_cons' top_env (WF (env, ty1)))@(split_cons' top_env (WF (env2, ty2)))
  |WF (env, Liq.TScalar (base_ty, phi)) ->
    (match Liq.b2sort base_ty with
     |None -> raise (Constraint "dont know what sort is this")
     |Some b_sort ->
       let senv =(Liq.mk_sort_env env) in
       (match base_ty with
        |Liq.TData (data, tys, pas) ->
          let tys_simple_cons = 
            List.concat (List.map (fun ty -> split_cons' top_env (WF (env, ty))) tys)
          in
          let pas_simple_cons =
            List.map (fun (args_sort, p) -> SWF(top_env, (args_sort@senv, p))) pas
          in
          (SWF (top_env, ((Id.valueVar_id, b_sort)::senv, phi)))::(tys_simple_cons@pas_simple_cons)
        |Liq.TBool|Liq.TInt|Liq.TAny _ ->
          [SWF (top_env,((Id.valueVar_id, b_sort)::senv, phi))]
        |Liq.TVar _ -> assert false (* becase TVar will be unused *)))
  |WF (env, Liq.TBot) -> []

  |Sub (env,
        Liq.TFun ((x, ty1_in), ty1_out),
        Liq.TFun ((y, ty2_in), ty2_out)  ) -> (* ty1_in -> ty1_out <: ty2_in -> ty2_out *)
    let simple_cons_in = split_cons' top_env (Sub (env, ty2_in, ty1_in)) in
    let env2 = Liq.env_add env (y, ty2_in) in
    let ty1_out' =
      if x = y then
        ty1_out
      else
        let y_sort = (match Liq.type2sort ty2_in with Some s -> s| _ -> assert false) in
        let y_var = Formula.Var (y_sort, y) in
        Liq.substitute_F (M.singleton x y_var) ty1_out in (* [y/x]ty1_out *)
    let simple_cons_out = split_cons' top_env (Sub (env2, ty1_out', ty2_out)) in
    simple_cons_in@simple_cons_out
  |Sub (env,
        Liq.TScalar (b1, phi1),
        Liq.TScalar (b2, phi2) ) ->
    (* let phi_env = Liq.env2formula env (S.union (Formula.fv phi1) (Formula.fv phi2)) in *)
    (match b1,b2 with
     |(Liq.TData (data, tys1, pas1)),(Liq.TData (data', tys2, pas2)) when data = data' ->
       let tys_simple_cons =
         List.concat (List.map2 (fun ty1 ty2 -> split_cons' top_env (Sub (env, ty1, ty2))) tys1 tys2)
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
       

let split_cons c =
  match c with
  |WF (env, ty) -> split_cons' env c
  |Sub (env, ty1, ty2) -> split_cons' env c


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

       