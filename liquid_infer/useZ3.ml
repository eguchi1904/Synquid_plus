open Z3
open Z3.Arithmetic
open Z3.Symbol
open Z3.Expr
open Z3.Solver


type sort_map = ((Formula.sort),(Sort.sort)) Hashtbl.t (* hashを試してみる *)
type id_expr_map = ((Id.t),(Expr.expr)) Hashtbl.t
type id_fun_map = ((Id.t), (FuncDecl.func_decl)) Hashtbl.t

type z3_env = sort_map * id_expr_map * id_fun_map
            
let ctx = mk_context [] 

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
  |Formula.DataS (i, ss) as s->
    (try Hashtbl.find smap s  with
       Not_found ->
       (Printf.printf "let's make z3 sort! %s\n" (Formula.sort2string s));
       let new_z3_sort = Sort.mk_uninterpreted_s ctx (gen_string i) in
       (Hashtbl.add smap s new_z3_sort);
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
  match e with
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
    (try (Hashtbl.find emap i) ,z_sort with
      Not_found ->
      let new_var = (Expr.mk_const_s ctx i z_sort) in
      (Hashtbl.add emap i new_var);
      new_var, z_sort)

  |Formula.Unknown (sita, i) ->
    let z_sort = sort2z3 ctx smap Formula.BoolS in
    (try (Hashtbl.find emap i) ,z_sort with
      Not_found ->
      let new_var = (Expr.mk_const_s ctx i z_sort) in
      (Hashtbl.add emap i new_var);
      new_var, z_sort)    
      
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

(* let substitute_z3 ((smap,emap,fmap):z3_env) (sita:) (z3_e:Expr.expr) = *)
(*   let sita_list = M.bindings sita in *)
(*   let vars, ps = List.split *)
(*                    List.map (fun i e ->(Hashtbl.find emap i), *)
                                       
                


let convert ((smap,emap,fmap):z3_env) (e:Formula.t) =
  formula2z3 ctx smap emap fmap e
  
exception CANT_SOLVE
        
let is_valid (e:Expr.expr) =
  let solver = mk_solver ctx None in
  let not_e =  (Boolean.mk_not ctx e) in
  (Solver.add solver [not_e]);
  let ret = Solver.check solver [] in
  if ret = UNSATISFIABLE then
    true
  else if ret = SATISFIABLE then
    false
  else
    raise CANT_SOLVE
  
  
