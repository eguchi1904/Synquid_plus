(* UFLIA *)
type sort = BoolS | IntS | DataS of Id.t * (sort list) | SetS of sort | AnyS

(* type unop = Neg | Not *)
                                                                      
(* type binop = *)
(*     Times | Plus | Minus |          (\* Int -> Int -> Int      *\) *)
(*     Eq | Neq |                     (\* a -> a -> Bool *\) *)
(*     Lt | Le | Gt | Ge |            (\* Int -> Int -> Bool *\) *)
(*     And | Or | Implies | Iff |     (\* Bool -> Bool -> Bool *\) *)
(*     Union | Intersect | Diff |     (\* Set -> Set -> Set *\) *)
(*     Member | Subset                (\* Int/Set -> Set -> Bool *\) *)

(* formula -- predicate unknownはなくて良いかな *)
type t =
  |Bool of bool
  |Int of int
  |Set of sort * (t list)         (* set literal [1, 2, 3] *)
  |Var of sort * Id.t             (* input variable *)
  |Unknown of subst * Id.t        (* predicate unknown with pending substitution *)
  |Cons of sort * Id.t * (t list) (* datatype constructor *)
  |UF of sort * Id.t * (t list) (* uninterpreted function *)
  |All of (Id.t * sort) list * t
  |Exist of (Id.t * sort) list * t
          
  (* 以下、解釈付きの演算 *)
  |If of t * t * t
  |Times of t * t
  |Plus of t * t
  |Minus of t * t
  |Eq of t * t
  |Neq of t * t
  |Lt of t * t
  |Le of t * t
  |Gt of t * t
  |Ge of t * t
  |And of t * t
  |Or of t * t
  |Implies of t * t
  |Iff of t * t
  |Union of t * t
  |Intersect of t * t
  |Diff of t * t
  |Member of t * t
  |Subset of t * t
  |Neg of t 
  |Not of t 
and subst = t M.t (* 術後変数の代入 *)

type pa =                       (* for predicate abstraction *)
  (Id.t * sort) list  * t

let rec fv = function               (* 自由変数、 *)
  |Var (_,i) when i = Id.valueVar_id -> S.empty (* _v は自由変数でない *)
  |Var (_,i) -> S.singleton i
  |Bool _ | Int _ |Unknown _ -> S.empty
  |Set (_, ts) |Cons (_,_, ts) |UF (_,_,ts) ->
    List.fold_left (fun acc t -> S.union acc (fv t)) S.empty ts
  |If (t1,t2,t3) ->S.union (fv t1) (S.union (fv t2) (fv t3) )
  |Times(t1,t2) |Plus(t1,t2) |Minus (t1,t2) |Eq(t1,t2) | Neq(t1,t2)|Lt(t1,t2)
   |Le(t1,t2)|Gt(t1,t2)|Ge(t1,t2)|And(t1,t2)|Or(t1,t2)|Implies(t1,t2)|Iff(t1,t2)
   |Union(t1,t2) |Intersect(t1,t2) |Diff(t1,t2) |Member(t1,t2) |Subset(t1,t2)
   ->S.union (fv t1) (fv t2)
  |Neg t1 |Not t1 ->fv t1
  |All (args,t1) |Exist (args,t1) ->
    S.diff (fv t1) (S.of_list (List.map fst args))


let rec and_list (es:t list) =
  match es with
  |[] -> Bool true
  |(Bool true)::es' -> and_list es'
  |e::es' -> And (e, and_list es')

  

let subst_compose (sita1:subst) (sita2:subst) = (* sita t = sita1(sita2 t) *)
  let sita2' = M.mapi
                 (fun i t ->
                   match t with
                   |Var( _,i')|Unknown (_,i') when M.mem i' sita1 ->
                     M.find i' sita1
                   |_ -> t)
                 sita2         
  in
  M.union (fun i t1 t2 -> Some t2) sita1 sita2'
  

let genFvar s i = Var (s, (Id.genid i))

                

let genUnkownP i = Unknown (M.empty, (Id.genid i))
                 
let genUnknownPa ((args,p):pa) s = (args, genUnkownP s) (* for predicate abstraction *)


let rec substitution (sita:subst) (t:t) =
(* substitueは、Var i に対して、Any iではなく *)
  match t with
  |Var (s,i) when (* s = BoolS && *) M.mem i sita ->
    
    M.find i sita           (* 代入 *)

  |Unknown (sita1, i) when M.mem i sita ->
    let p = M.find i sita in
    substitution sita1 p        (* pending substitution を展開する。 *)

  |Unknown (sita1, i) ->
    let sita' = subst_compose sita sita1 in
    Unknown (sita', i)          (* pending substitution を合成 *)

  (* 残りはただの再起 *)
  |Set (s, ts) ->
    let ts' = List.map (substitution sita) ts in
    Set (s, ts')
  |Cons (s, i, ts) ->
    let ts' = List.map (substitution sita) ts in
    Cons(s, i, ts')
  |UF (s, i, ts) ->
    let ts' = List.map (substitution sita) ts in
    UF(s, i, ts')
  |All (is, t') ->All (is, (substitution sita t'))
  |Exist (is, t') ->Exist (is, (substitution sita t'))
  |If (t1, t2, t3) ->If ((substitution sita t1),
                         (substitution sita t2),
                         (substitution sita t3))
  |Times (t1, t2) -> Times ((substitution sita t1),
                            (substitution sita t2))
  |Plus (t1, t2) -> Plus ((substitution sita t1),
                          (substitution sita t2))
  |Minus (t1, t2) -> Minus ((substitution sita t1),
                            (substitution sita t2))
  |Eq (t1, t2) -> Eq ((substitution sita t1),
                      (substitution sita t2))
  |Neq (t1, t2) -> Neq ((substitution sita t1),
                        (substitution sita t2))
  |Lt (t1, t2) -> Lt ((substitution sita t1),
                      (substitution sita t2))
  |Le (t1, t2) -> Le ((substitution sita t1),
                      (substitution sita t2))
  |Gt (t1, t2) -> Gt ((substitution sita t1),
                      (substitution sita t2))
  |Ge (t1, t2) -> Ge ((substitution sita t1),
                      (substitution sita t2))
  |And (t1, t2) -> And ((substitution sita t1),
                        (substitution sita t2))
  |Or (t1, t2) -> Or ((substitution sita t1),
                      (substitution sita t2))
  |Implies (t1, t2) -> Implies ((substitution sita t1),
                                (substitution sita t2))
  |Iff (t1, t2) -> Iff ((substitution sita t1),
                        (substitution sita t2))
  |Union (t1, t2) -> Union ((substitution sita t1),
                            (substitution sita t2))
  |Intersect (t1, t2) -> Intersect ((substitution sita t1),
                                    (substitution sita t2))
  |Diff (t1, t2) -> Diff ((substitution sita t1),
                          (substitution sita t2))
  |Member (t1, t2) -> Member ((substitution sita t1),
                              (substitution sita t2))
  |Subset (t1, t2) -> Subset ((substitution sita t1),
                              (substitution sita t2))
  |Neg t1 -> Neg (substitution sita t1)
  |Not t1 -> Not (substitution sita t1)
  |t ->t

let pa_substitution (sita:subst) ((args,t):pa) =
  (* 引数と変数名がかぶるものは置換しない *)
  let sita' = M.filter
                (fun i  _ -> not (List.mem (i, BoolS) args ) )
                sita
  in
  let t' = substitution sita' t in
  (args, t')

(* 単縦に変数の置換 *)
let rec replace (x:Id.t) (y:Id.t) (t:t) =
  match t with
  |Var (s,i) when i = x ->
    Var (s,y)
  (* 残りはただの再起 *)
  |Set (s, ts) ->
    let ts' = List.map (replace x y) ts in
    Set(s, ts')
  |Cons (s, i, ts) ->
    let ts' = List.map (replace x y) ts in
    Cons(s, i, ts')
  |UF (s, i, ts) ->
    let ts' = List.map (replace x y) ts in
    UF(s, i, ts')
  |All (is, t') ->All (is, (replace x y t'))
  |Exist (is, t') ->Exist (is, (replace x y t'))
  |If (t1, t2, t3) ->If ((replace x y t1),
                         (replace x y t2),
                         (replace x y t3))
  |Times (t1, t2) -> Times ((replace x y t1),
                            (replace x y t2))
  |Plus (t1, t2) -> Plus ((replace x y t1),
                          (replace x y t2))
  |Minus (t1, t2) -> Minus ((replace x y t1),
                            (replace x y t2))
  |Eq (t1, t2) -> Eq ((replace x y t1),
                      (replace x y t2))
  |Neq (t1, t2) -> Neq ((replace x y t1),
                        (replace x y t2))
  |Lt (t1, t2) -> Lt ((replace x y t1),
                      (replace x y t2))
  |Le (t1, t2) -> Le ((replace x y t1),
                      (replace x y t2))
  |Gt (t1, t2) -> Gt ((replace x y t1),
                      (replace x y t2))
  |Ge (t1, t2) -> Ge ((replace x y t1),
                      (replace x y t2))
  |And (t1, t2) -> And ((replace x y t1),
                        (replace x y t2))
  |Or (t1, t2) -> Or ((replace x y t1),
                      (replace x y t2))
  |Implies (t1, t2) -> Implies ((replace x y t1),
                                (replace x y t2))
  |Iff (t1, t2) -> Iff ((replace x y t1),
                        (replace x y t2))
  |Union (t1, t2) -> Union ((replace x y t1),
                            (replace x y t2))
  |Intersect (t1, t2) -> Intersect ((replace x y t1),
                                    (replace x y t2))
  |Diff (t1, t2) -> Diff ((replace x y t1),
                          (replace x y t2))
  |Member (t1, t2) -> Member ((replace x y t1),
                              (replace x y t2))
  |Subset (t1, t2) -> Subset ((replace x y t1),
                              (replace x y t2))
  |Neg t1 -> Neg (replace x y t1)
  |Not t1 -> Not (replace x y t1)           
  |t ->t


let pa_replace x y ((args,t):pa) =
  (* 引数と変数名がかぶるものは置換しない *)
  if List.mem_assoc x args then
    (args, t)
  else
    let t' = replace x y t in
    (args, t')
       
