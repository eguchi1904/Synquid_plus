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
  |Set of sort * (t list)
  |Any of sort * Id.t        (* input variable *)
  |Var of sort * Id.t        (* predicate unknown *)
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
        

type pa =                       (* for predicate abstraction *)
  (Id.t * sort) list  * t

type subst = t M.t (* 術後変数の代入　Boolソートが対象,ではないか *)

let genFvar s = Var (BoolS, (Id.genid s))

let genPavar ((args,p):pa) s = (args, genFvar s)
  

let rec substitution (sita:subst) (t:t) =
(* substitueは、Var i に対して、Any iではなく *)
  match t with
  |Var (s,i) when (* s == BoolS && *) M.mem i sita ->
    M.find i sita           (* 代入 *)

  (* 残りはただの再起 *)
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
  |t' -> t'
       

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
  |Var (s,i) when i==x ->
    Var (s,y)
  (* 残りはただの再起 *)
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
  |t' -> t'


let pa_replace x y ((args,t):pa) =
  (* 引数と変数名がかぶるものは置換しない *)
  if List.mem_assoc x args then
    (args, t)
  else
    let t' = replace x y t in
    (args, t')
       
