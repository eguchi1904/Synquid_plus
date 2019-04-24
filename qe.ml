open Formula

let rec replace_UF (target:t) (replace:t) (t:t) = (* t1 = UF (i,[arg]) -> t2 *)
  if Formula_eq.f target  t then
    replace
  else
    (* ((Printf.printf "\n%s is not %s !\n " (p2string_with_sort t) (p2string_with_sort target)); *)
  match t with
  |Set (s, ts) ->
    let ts' = List.map (replace_UF target replace) ts in
    Set (s, ts')
  |Cons (s, i, ts) ->
    let ts' = List.map (replace_UF target replace) ts in
    Cons(s, i, ts')
  |UF (s, i, ts) ->
    let ts' = List.map (replace_UF target replace) ts in
    UF(s, i, ts')
  |All (is, t') ->All (is, (replace_UF target replace t'))
  |Exist (is, t') ->Exist (is, (replace_UF target replace t'))
  |If (t1, t2, t3) ->If ((replace_UF target replace t1),
                         (replace_UF target replace t2),
                         (replace_UF target replace t3))
  |Times (t1, t2) -> Times ((replace_UF target replace t1),
                            (replace_UF target replace t2))
  |Plus (t1, t2) -> Plus ((replace_UF target replace t1),
                          (replace_UF target replace t2))
  |Minus (t1, t2) -> Minus ((replace_UF target replace t1),
                            (replace_UF target replace t2))
  |Eq (t1, t2) -> Eq ((replace_UF target replace t1),
                      (replace_UF target replace t2))
  |Neq (t1, t2) -> Neq ((replace_UF target replace t1),
                        (replace_UF target replace t2))
  |Lt (t1, t2) -> Lt ((replace_UF target replace t1),
                      (replace_UF target replace t2))
  |Le (t1, t2) -> Le ((replace_UF target replace t1),
                      (replace_UF target replace t2))
  |Gt (t1, t2) -> Gt ((replace_UF target replace t1),
                      (replace_UF target replace t2))
  |Ge (t1, t2) -> Ge ((replace_UF target replace t1),
                      (replace_UF target replace t2))
  |And (t1, t2) -> And ((replace_UF target replace t1),
                        (replace_UF target replace t2))
  |Or (t1, t2) -> Or ((replace_UF target replace t1),
                      (replace_UF target replace t2))
  |Implies (t1, t2) -> Implies ((replace_UF target replace t1),
                                (replace_UF target replace t2))
  |Iff (t1, t2) -> Iff ((replace_UF target replace t1),
                        (replace_UF target replace t2))
  |Union (t1, t2) -> Union ((replace_UF target replace t1),
                            (replace_UF target replace t2))
  |Intersect (t1, t2) -> Intersect ((replace_UF target replace t1),
                                    (replace_UF target replace t2))
  |Diff (t1, t2) -> Diff ((replace_UF target replace t1),
                          (replace_UF target replace t2))
  |Member (t1, t2) -> Member ((replace_UF target replace t1),
                              (replace_UF target replace t2))
  |Subset (t1, t2) -> Subset ((replace_UF target replace t1),
                              (replace_UF target replace t2))
  |Neg t1 -> Neg (replace_UF target replace t1)
  |Not t1 -> Not (replace_UF target replace t1)
  |t ->t
    
let print_qformula bv pre_list  p =
  let bv_str = String.concat "," (S.elements bv) in
  (Printf.printf "\n\nbv=[%s]\n------------------------------\n" bv_str);
  (List.iter (fun formula -> Printf.printf "%s\n" (p2string_with_sort formula)) pre_list);
  (print_string "------------------------------\n");
  (Printf.printf "%s\n\n" (p2string_with_sort p))
  
let rec pop_var_eq bv = function
  |Eq (Var(s,i), e) :: p_list when S.mem i bv ->
    Some ( (i,e),p_list )
  |Eq (e, Var(s,i)) :: p_list when S.mem i bv ->
    Some ( (i,e),p_list )
  |p :: p_list ->
    (match pop_var_eq bv p_list with
     |Some (i_e, p_list') -> Some (i_e, p::p_list')
     |None ->None)
  |[] -> None
     
let rec var_eq_propagate bv pre_list p =
  (print_qformula bv pre_list p);
  match pop_var_eq bv pre_list with
  |Some ((i,e), pre_list') ->
    (Printf.printf "\npop:(%s,%s)\n" i (p2string_with_sort e));
    let pre_list'' = List.map (substitution (M.singleton i e)) pre_list' in
    let p' = substitution (M.singleton i e) p in
    var_eq_propagate bv pre_list'' p'
  |None -> pre_list,p

let all_bv_var bv es =
  List.for_all
    (* (fun e' ->S.subset (Formula.fv e') bv) *)
         (fun e' ->(match e' with
                    |Var (_,i') -> S.mem i' bv
                    |_ -> false))
         es

  
let rec pop_UF_eq bv = function (* uninterpreted function *)
  |Eq (UF(s,i,es), e) :: p_list when all_bv_var bv es ->
      Some ( (UF(s,i,es) ,e),p_list )
  |Eq (e, UF(s,i,es)) :: p_list when all_bv_var bv es ->
      Some ( (UF(s,i,es) ,e),p_list )

  |p :: p_list ->
    (match pop_UF_eq bv p_list with
     |Some (uf_e, p_list') -> Some (uf_e, p::p_list')
     |None ->None)
  |[] -> None
     
let rec var_UF_propagate bv pre_list p = (* uninterpreted function *)
  (print_qformula bv pre_list p);  
  match pop_UF_eq bv pre_list with
  |Some ((uf_app,e), pre_list') ->
    (Printf.printf "\npop: %s, %s\n" (p2string_with_sort uf_app) (p2string_with_sort e));
    let pre_list'' = List.map (replace_UF uf_app e) pre_list' in
    let p' = replace_UF uf_app e p in
    var_UF_propagate bv pre_list'' p'
  |None -> pre_list,p

let rec pop_UFUF_eq bv = function (* uninterpreted function *)
  |Eq ((UF(s,i,es) as uf), e) :: p_list when S.subset (fv uf) bv ->
      Some ( (UF(s,i,es) ,e),p_list )
  |Eq (e, (UF(s,i,es) as uf)) :: p_list when  S.subset (fv uf) bv ->
      Some ( (UF(s,i,es) ,e),p_list )

  |p :: p_list ->
    (match pop_UFUF_eq bv p_list with
     |Some (uf_e, p_list') -> Some (uf_e, p::p_list')
     |None ->None)
  |[] -> None
     
let rec var_UFUF_propagate bv pre_list p = (* uninterpreted function *)
  (print_qformula bv pre_list p);  
  match pop_UFUF_eq bv pre_list with
  |Some ((uf_app,e), pre_list') ->
    (Printf.printf "\npop: %s, %s\n" (p2string_with_sort uf_app) (p2string_with_sort e));
    let pre_list'' = List.map (replace_UF uf_app e) pre_list' in
    let p' = replace_UF uf_app e p in
    var_UFUF_propagate bv pre_list'' p'
  |None -> pre_list,p

let rec pop_left_eq bv = function (* uninterpreted function *)
  |Eq (e1, e2) :: p_list when S.is_cross (fv e1) bv ->
      Some (( e1 ,e2),p_list )
  |Eq (e1, e2) :: p_list when S.is_cross (fv e2) bv ->
      Some ( (e2 ,e1),p_list )
  |p :: p_list ->
    (match pop_left_eq bv p_list with
     |Some (e1_e2, p_list') -> Some (e1_e2, p::p_list')
     |None ->None)
  |[] -> None
     
let rec var_left_propagate bv pre_list p = (* uninterpreted function *)
  (print_qformula bv pre_list p);  
  match pop_left_eq bv pre_list with
  |Some ((e1,e2), pre_list') ->
    (Printf.printf "\npop: %s, %s\n" (p2string e1) (p2string e2));
    let pre_list'' = List.map (replace_UF e1 e2) pre_list' in
    let p' = replace_UF e1 e2 p in
    var_UFUF_propagate bv pre_list'' p'
  |None -> pre_list,p                           

exception DONT_KNOW of string


(*  var_eq_propagate ->
 var_UF_propagate ->
var_UFUF_propagate
の順に、置換する対象が複雑になる。
順次足していったのでコードが汚い。
この順番に置換してくことは本質*)
let f = function
  |QAll (args,pre_list, p) ->
    let bv = S.of_list (List.map fst args) in
    let pre_list', p' = var_eq_propagate bv pre_list p in
    let pre_list', p' = var_UF_propagate bv pre_list' p' in
    let pre_list', p' = var_UFUF_propagate bv pre_list' p' in
    let p' = Deformation.expand p' in
    let pre_list', p' = var_left_propagate bv pre_list' p' in    
    if S.is_empty (S.inter bv (fv p') ) then
      p'
    else
      ((print_qformula bv pre_list' p');
       raise (DONT_KNOW "qe"))

  |QExist (args, p_list) ->
    let bv = S.of_list (List.map fst args) in
    let dummy_p = Bool false in
    (* 等号伝播 *)
    let p_list',_ = var_eq_propagate bv p_list dummy_p in
    let p_list',_ = var_UF_propagate bv p_list' dummy_p in
    let p_list' = List.map Deformation.expand p_list' in
    let p_list', _ = var_left_propagate bv p_list' dummy_p in        
    (* 束縛変数が残っている式を削除。（==>方向） *)
    let p_list' = List.filter (fun e -> S.is_empty (S.inter bv (fv e))) p_list' in
    Formula.and_list p_list'

    

  
