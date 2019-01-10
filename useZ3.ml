open Z3
open Z3.Arithmetic
open Z3.Symbol
open Z3.Expr
open Z3.Solver


type sort_map = ((Formula.sort),(Sort.sort)) Hashtbl.t (* hashを試してみる *)
type id_expr_map = ((Id.t),(Expr.expr)) Hashtbl.t
type id_fun_map = ((Id.t), (FuncDecl.func_decl)) Hashtbl.t

type z3_env = sort_map * id_expr_map * id_fun_map

(* z3 global context *)
let ctx = mk_context [("trace","true"); ("well_sorted_check","true");("debug_ref_count","true")]
let () = (toggle_warning_messages true)
        
        

let mk_z3_env () :z3_env=
  (Hashtbl.create 12345),(Hashtbl.create 12345),(Hashtbl.create 12345)
                
let counter = ref 0
let gen_string s =
  incr counter;
  Printf.sprintf "%s.%d" s !counter



(*　副作用 適宜hashを更新する。 *)
let rec sort2z3 (ctx:context) (smap:sort_map) (s:Formula.sort) =
  match s with
  |Formula.BoolS -> Boolean.mk_sort ctx
  |Formula.IntS -> Integer.mk_sort ctx
  |Formula.DataS (i, _) ->
    (* D Ti ignore Ti*)
    let dummy = Formula.IntS in
    (try Hashtbl.find smap (Formula.DataS (i, [dummy]))  with
       Not_found ->
       (* (Printf.printf "let's make z3 sort! %s\n" (Formula.sort2string s)); *)
       let new_z3_sort = Sort.mk_uninterpreted_s ctx (gen_string i) in
       (Hashtbl.add smap (Formula.DataS (i, [dummy])) new_z3_sort);
       new_z3_sort)
  |Formula.SetS s1 ->
    let z_s1 = sort2z3 ctx smap s1 in
    Z3.Set.mk_sort ctx z_s1
  |Formula.AnyS i ->
    Integer.mk_sort ctx
  |Formula.UnknownS i ->
    (Printf.fprintf stderr "there is Unknown sort:%s\n\n" i);
    (assert false);
    Integer.mk_sort ctx
    (* (try Hashtbl.find smap s  with *)
    (*    Not_found -> *)
    (*    let new_z3_sort = Sort.mk_uninterpreted_s ctx (gen_string i) in *)
    (*    (Hashtbl.add smap s new_z3_sort); *)
    (*    new_z3_sort)     *)

(* 副作用：　適宜smap,emap,fmapを更新 *)
let rec formula2z3 (ctx:context) (smap:sort_map) (emap:id_expr_map) (fmap:id_fun_map) (e:Formula.t) 
        :Expr.expr * Sort.sort =
  try
  (match e with
  |Formula.Bool b ->
    (Boolean.mk_val ctx b), (Boolean.mk_sort ctx)
   
  |Formula.Int i ->
    (Integer.mk_numeral_i ctx i), (Integer.mk_sort ctx)
   
  |Formula.Set (s, es1) ->
    let (z_es1, z_ss) = List.split (List.map (formula2z3 ctx smap emap fmap) es1) in
    let z_s = sort2z3 ctx smap s in
    let z_e = List.fold_left
                (fun z_e z_e1 -> Z3.Set.mk_set_add ctx z_e z_e1) (* z_e + [z_e1] *)
                (Z3.Set.mk_empty ctx z_s)
                z_es1 
    in
    z_e, (Z3.Set.mk_sort ctx z_s)
    
  |Formula.Var (sort, i) ->
    let z_sort = sort2z3 ctx smap sort in

    (try
       let z3_i =  (Hashtbl.find emap i) in
       (* (Printf.printf "\n%s z_sort is %s\n" i (Z3.Sort.to_string (get_sort z3_i))); *)
       (z3_i,z_sort)
     with
      Not_found ->
      let new_var = (Expr.mk_const_s ctx i z_sort) in
      (Hashtbl.add emap i new_var);
      new_var, z_sort)

  |Formula.Unknown (senv, sort_sita, sita, i) ->
    (Printf.printf "p2z3: encounter unknown predicate: %s\n" i);
    assert false
    (* let z_sort = sort2z3 ctx smap Formula.BoolS in *)
    (* (try (Hashtbl.find emap i) ,z_sort with *)
    (*   Not_found -> *)
    (*   let new_var = (Expr.mk_const_s ctx i z_sort) in *)
    (*   (Hashtbl.add emap i new_var); *)
    (*   new_var, z_sort)     *)
      
  |Formula.Cons (sort, i , args) ->
    let (z_args_e, z_args_s) = List.split (List.map (formula2z3 ctx smap emap fmap) args) in
    let z_sort = sort2z3 ctx smap sort in
    (try 
       let z_cons = Hashtbl.find fmap i in
       (mk_app ctx z_cons z_args_e), z_sort
     with
       Not_found ->
       let new_fun = (FuncDecl.mk_func_decl_s ctx i z_args_s z_sort) in
       (Hashtbl.add fmap i new_fun);
       (mk_app ctx new_fun z_args_e), z_sort)

  |Formula.UF (sort, i, args) ->
    let (z_args_e, z_args_s) = List.split (List.map (formula2z3 ctx smap emap fmap) args) in
    let z_sort = sort2z3 ctx smap sort in
    (try 
       let z_cons = Hashtbl.find fmap i in
       (mk_app ctx z_cons z_args_e), z_sort
     with
       Not_found ->
       let new_fun = (FuncDecl.mk_func_decl_s ctx i z_args_s z_sort) in
       (Hashtbl.add fmap i new_fun);
       (mk_app ctx new_fun z_args_e), z_sort)

  |Formula.All _|Formula.Exist _ -> raise (Invalid_argument "qualifiyer")

  |Formula.If (e1,e2,e3) ->
    let z_e1 ,z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2 ,z_s2 = formula2z3 ctx smap emap fmap e2 in
    let z_e3 ,z_s3 = formula2z3 ctx smap emap fmap e3 in
    (assert (z_s2 = z_s3));
    (Boolean.mk_ite ctx z_e1 z_e2 z_e3), z_s2

  |Formula.Times (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Integer.mk_sort ctx)));
    (mk_mul ctx [z_e1; z_e2]), z_s1

  |Formula.Plus (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Integer.mk_sort ctx)));
    (mk_add ctx [z_e1; z_e2]), z_s1

  |Formula.Minus (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Integer.mk_sort ctx)));
    (mk_sub ctx [z_e1; z_e2]), z_s1
    
  |Formula.Eq (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 ));
    (Boolean.mk_eq ctx z_e1 z_e2), (Boolean.mk_sort ctx)
    
  |Formula.Neq (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 ));
    (Boolean.mk_not ctx (Boolean.mk_eq ctx z_e1 z_e2)), (Boolean.mk_sort ctx)

  |Formula.Lt (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 ));
     (mk_lt ctx z_e1 z_e2), (Boolean.mk_sort ctx)

  |Formula.Le (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2  ));
     (mk_le ctx z_e1 z_e2), (Boolean.mk_sort ctx)     
     
  |Formula.Gt (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 ));
    (mk_gt ctx z_e1 z_e2), (Boolean.mk_sort ctx)

  |Formula.Ge (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 ));
    (mk_ge ctx z_e1 z_e2), (Boolean.mk_sort ctx)

  |Formula.And (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Boolean.mk_sort ctx)));
    (Boolean.mk_and ctx [z_e1; z_e2]), (Boolean.mk_sort ctx)

  |Formula.Or (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Boolean.mk_sort ctx)));
    (Boolean.mk_or ctx [z_e1; z_e2]), (Boolean.mk_sort ctx)

 |Formula.Implies (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Boolean.mk_sort ctx)));
    (Boolean.mk_implies ctx z_e1 z_e2), (Boolean.mk_sort ctx)

 |Formula.Iff (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2 && z_s1 = (Boolean.mk_sort ctx)));
    (Boolean.mk_iff ctx z_e1 z_e2), (Boolean.mk_sort ctx)

 |Formula.Union (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2));
    (Set.mk_union ctx [z_e1; z_e2]), z_s1

 |Formula.Intersect (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2));
    (Set.mk_intersection ctx [z_e1; z_e2]), z_s1

 |Formula.Diff (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2));
    (Set.mk_difference ctx z_e1 z_e2), z_s1

 |Formula.Member (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (Set.mk_membership ctx z_e1 z_e2), z_s1
    
 |Formula.Subset (e1,e2) ->
    let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
    let z_e2, z_s2 = formula2z3 ctx smap emap fmap e2 in
    (assert (z_s1 = z_s2));
    (Set.mk_subset ctx z_e1 z_e2), z_s1

 |Formula.Neg e1 ->
   let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
   (assert (z_s1 = (Integer.mk_sort ctx)));
   (mk_unary_minus ctx z_e1), z_s1
 
 |Formula.Not e1 ->
   let z_e1, z_s1 = formula2z3 ctx smap emap fmap e1 in
   (assert (z_s1 = (Boolean.mk_sort ctx)));
   (Boolean.mk_not ctx z_e1), z_s1

  )
  with Z3.Error mess ->
       (Printf.printf "Error!when try to convert:\n%s\nZ3_Mess:%s\n" (Formula.p2string_with_sort e) mess);
       assert false
(* let substitute_z3 ((smap,emap,fmap):z3_env) (sita:) (z3_e:Expr.expr) = *)
(*   let sita_list = M.bindings sita in *)
(*   let vars, ps = List.split *)
(*                    List.map (fun i e ->(Hashtbl.find emap i), *)
                                       
                


(* let convert ((smap,emap,fmap):z3_env) (e:Formula.t) = *)
(*   (Printf.printf "\n\nconvert:%s\n" (Formula.p2string_with_sort e)); *)
(*   formula2z3 ctx smap emap fmap e *)

  
let convert (e:Formula.t) =
  let ((smap,emap,fmap):z3_env) = mk_z3_env () in
  (* (Printf.printf "\n\nconvert:%s\n" (Formula.p2string_with_sort e)); *)
  formula2z3 ctx smap emap fmap e
  
exception CANT_SOLVE
let z3_t = ref 0.0
let st = ref 0.0
let start_z3_clock () = 
 st := Sys.time ()

let stop_z3_clock () =
  let ed = Sys.time () in
  (z3_t := !z3_t +. (ed -. !st))
  

         
let is_valid (e:Expr.expr) =
  (start_z3_clock ());
  (* (Printf.printf "\n\nis_valid:\n%s" (Z3.Expr.to_string e)); *)
  let solver = mk_solver ctx None in
  let not_e =  (Boolean.mk_not ctx e) in
  (* let st = Sys.time () in *)
  (Z3.Solver.add solver [not_e]);
  (* let ed = Sys.time () in *)
  (* (Printf.printf "z3:end_solving:%f\n" (ed -. st )); *)
  let ret = Z3.Solver.check solver [] in
  (stop_z3_clock ());
  if ret = UNSATISFIABLE then
    true
  else if ret = SATISFIABLE then
    false
  else
    raise CANT_SOLVE
  

let satisfiable_but_not_valid (e:Expr.expr) =
  (start_z3_clock ());
    let solver = mk_solver ctx None in
    (Z3.Solver.add solver [e]);
    let ret = Z3.Solver.check solver [] in
    (stop_z3_clock ());
    if ret = UNSATISFIABLE then
      false
    else if ret = SATISFIABLE then
      not (is_valid e)
  else
    raise CANT_SOLVE
    
