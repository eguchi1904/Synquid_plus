(* UFLIA *)
type sort = BoolS | IntS | DataS of Id.t * (sort list) | SetS of sort | AnyS of Id.t

(* type unop = Neg | Not *)
                                                                      
(* type binop = *)
(*     Times | Plus | Minus |          (\* Int -> Int -> Int      *\) *)
(*     Eq | Neq |                     (\* a -> a -> Bool *\) *)
(*     Lt | Le | Gt | Ge |            (\* Int -> Int -> Bool *\) *)
(*     And | Or | Implies | Iff |     (\* Bool -> Bool -> Bool *\) *)
(*     Union | Intersect | Diff |     (\* Set -> Set -> Set *\) *)
(*     Member | Subset                (\* Int/Set -> Set -> Bool *\) *)

(* formula -- predicate unknownはなくて良いかな <= 嘘 *)
type t =
  |Bool of bool
  |Int of int
  |Set of sort * (t list)         (* set literal [1, 2, 3] *)
  |Var of sort * Id.t             (* input variable *)
  |Unknown of subst * Id.t        (* predicate unknown with pending substitution *)
  |Cons of sort * Id.t * (t list) (* datatype constructor *)
  |UF of sort * Id.t * (t list)   (* uninterpreted function *)
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


type pa = (Id.t * sort) list * t

(* \x.y.r x y の形だった場合、rを返す。 *)
let eta_shape ((arg,t):pa) =
  match t with
  |UF (_,r,ts) ->
    if List.for_all2 (fun (i,sort) t ->t = Var(sort,i)) arg ts then
      Some r
    else
      None
  |_ -> None
      
type pa_shape = (sort list) * sort

let rec p2string = function
  |Bool b -> string_of_bool b | Int i -> string_of_int i
  |Set (_,ts) ->let ts_string = String.concat ", " (List.map p2string ts) in
                Printf.sprintf "[%s]" ts_string
  |Var (_,id) ->Printf.sprintf "%s " id
  |Unknown (_,id)->Printf.sprintf "P[%s]" id
  |Cons (_,id,ts)|UF (_,id,ts) ->
    let ts_string = String.concat " " (List.map p2string ts) in
    Printf.sprintf "(%s %s)" id ts_string
  |All (args,t) ->
    Printf.sprintf "All(somearg).\n%s" (p2string t)
  |Exist (args,t) ->
    Printf.sprintf "Exist(somearg).\n%s" (p2string t)
  |If (t1,t2,t3) ->
    Printf.sprintf "if(%s)then %s else %s" (p2string t1) (p2string t2) (p2string t3)
  |Times (t1,t2) ->
    Printf.sprintf "(%s)*(%s)" (p2string t1) (p2string t2)
  |Plus (t1,t2) ->
    Printf.sprintf "%s + %s" (p2string t1) (p2string t2)
  |Minus (t1,t2) ->
    Printf.sprintf "(%s)-(%s)" (p2string t1) (p2string t2)
  |Eq (t1,t2) ->
    Printf.sprintf "%s == %s" (p2string t1) (p2string t2)
  |Neq (t1,t2) ->
    Printf.sprintf "(%s)!=(%s)" (p2string t1) (p2string t2)
  |Lt (t1,t2) ->
    Printf.sprintf "(%s)<(%s)" (p2string t1) (p2string t2)
  |Le (t1,t2) ->
    Printf.sprintf "(%s)<=(%s)" (p2string t1) (p2string t2)
  |Gt (t1,t2) ->
    Printf.sprintf "(%s)>(%s)" (p2string t1) (p2string t2)
  |Ge (t1,t2) ->
    Printf.sprintf "(%s)>=(%s)" (p2string t1) (p2string t2)
  |And (t1,t2) ->
    Printf.sprintf "(%s)&&(%s)" (p2string t1) (p2string t2)
  |Or (t1,t2) ->
    Printf.sprintf "(%s)||(%s)" (p2string t1) (p2string t2)
  |Implies (t1,t2) ->
    Printf.sprintf "(%s)==>(%s)" (p2string t1) (p2string t2)
  |Iff (t1,t2) ->
    Printf.sprintf "(%s)<=>(%s)" (p2string t1) (p2string t2)
  |Union (t1,t2) ->
    Printf.sprintf "(%s)\/(%s)" (p2string t1) (p2string t2)
  |Intersect (t1,t2) ->
    Printf.sprintf "(%s)/\(%s)" (p2string t1) (p2string t2)
  |Diff (t1,t2) ->
    Printf.sprintf "(%s)/(%s)" (p2string t1) (p2string t2)
  |Member (t1,t2) ->
    Printf.sprintf "(%s)in %s" (p2string t1) (p2string t2)
  |Subset (t1,t2) ->
    Printf.sprintf "(%s)<= (%s)" (p2string t1) (p2string t2)
  |Neg t ->
    Printf.sprintf "-(%s)" (p2string t )
  |Not t ->
    Printf.sprintf "!(%s)" (p2string t )


   
              
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
  |[e] -> e
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

let id2pa_shape i ((arg_sorts,rets):pa_shape) :pa =
  let args = List.mapi (fun n s -> (Id.genid (string_of_int n) , s)) arg_sorts in
  let uf_args = List.map (fun (x,s) ->Var(s,x)) args in
  let body = UF (rets, i, uf_args) in
  (args,body)
  

let genUnkownP i = Unknown (M.empty, (Id.genid i))
                 
let genUnknownPa ((args,p):pa) s = (args, genUnkownP s) (* for predicate abstraction *)

let genUnknownPa_shape ((arg_sort,rets):pa_shape) s =
  let args,_ = List.fold_right
               (fun  sort (args,i) -> ((Id.genid (string_of_int i)),sort)::args,i+1)
               arg_sort
               ([],0)
  in
  (args, genUnkownP s)
      
(* let genUnknownPreAbst i ((arg_s,s):pa_shape) = *)
(*   let args = List.map (fun s ->(Id.genid "ar"),s) arg_s in *)
(*   let unknownP = genUnkownP i in *)
(*   Abs (args,unknownP) *)


let rec substitution (sita:subst) (t:t) =
(* substitueは、Var i に対して、Any iではなく *)
  match t with
  |Var (s,i) when (* s = BoolS && *) M.mem i sita ->
    (match M.find i sita with
     |Var (_,i') -> Var (s,i')  (* 代入先のsortを参照する。 *)
     | p -> p)

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

let rec pa_substitution (pa_sita:pa M.t) (t:t) =
  (* predicate abstraction の代入。代入先はuniterpreted function *)
  match t with
  |UF (s, i, ts) when M.mem i pa_sita ->
    let ts' = List.map (pa_substitution pa_sita) ts in
    let (args,body) = M.find i pa_sita in
    let sita = M.add_list2 (List.map fst args) ts' M.empty in
    substitution sita body
  |UF (s, i, ts) ->
    let ts' = List.map (pa_substitution pa_sita) ts in
    UF (s, i, ts')
  (* 残りは再起 *)
  |Set (s, ts) ->
    let ts' = List.map (pa_substitution pa_sita) ts in
    Set (s, ts')
  |Cons (s, i, ts) ->
    let ts' = List.map (pa_substitution pa_sita) ts in
    Cons(s, i, ts')    
  |All (is, t') -> All (is, (pa_substitution pa_sita t'))
  |Exist (is, t') -> Exist (is, pa_substitution pa_sita t')
  |If (t1, t2, t3) ->If((pa_substitution pa_sita t1),
                        (pa_substitution pa_sita t2),
                        (pa_substitution pa_sita t3))
  |Times (t1,t2) ->Times ((pa_substitution pa_sita t1),
                          (pa_substitution pa_sita t2))
  |Plus (t1, t2) -> Plus ((pa_substitution pa_sita t1),
                          (pa_substitution pa_sita t2))
  |Minus (t1, t2) -> Minus ((pa_substitution pa_sita t1),
                            (pa_substitution pa_sita t2))
  |Eq (t1, t2) -> Eq ((pa_substitution pa_sita t1),
                      (pa_substitution pa_sita t2))
  |Neq (t1, t2) -> Neq ((pa_substitution pa_sita t1),
                        (pa_substitution pa_sita t2))
  |Lt (t1, t2) -> Lt ((pa_substitution pa_sita t1),
                      (pa_substitution pa_sita t2))
  |Le (t1, t2) -> Le ((pa_substitution pa_sita t1),
                      (pa_substitution pa_sita t2))
  |Gt (t1, t2) -> Gt ((pa_substitution pa_sita t1),
                      (pa_substitution pa_sita t2))
  |Ge (t1, t2) -> Ge ((pa_substitution pa_sita t1),
                      (pa_substitution pa_sita t2))
  |And (t1, t2) -> And ((pa_substitution pa_sita t1),
                        (pa_substitution pa_sita t2))
  |Or (t1, t2) -> Or ((pa_substitution pa_sita t1),
                      (pa_substitution pa_sita t2))
  |Implies (t1, t2) -> Implies ((pa_substitution pa_sita t1),
                                (pa_substitution pa_sita t2))
  |Iff (t1, t2) -> Iff ((pa_substitution pa_sita t1),
                        (pa_substitution pa_sita t2))
  |Union (t1, t2) -> Union ((pa_substitution pa_sita t1),
                            (pa_substitution pa_sita t2))
  |Intersect (t1, t2) -> Intersect ((pa_substitution pa_sita t1),
                                    (pa_substitution pa_sita t2))
  |Diff (t1, t2) -> Diff ((pa_substitution pa_sita t1),
                          (pa_substitution pa_sita t2))
  |Member (t1, t2) -> Member ((pa_substitution pa_sita t1),
                              (pa_substitution pa_sita t2))
  |Subset (t1, t2) -> Subset ((pa_substitution pa_sita t1),
                              (pa_substitution pa_sita t2))
  |Neg t1 -> Neg (pa_substitution pa_sita t1)
  |Not t1 -> Not (pa_substitution pa_sita t1)
  |t' ->t'


(* 単縦に変数の置換 *)
let rec replace (x:Id.t) (y:Id.t) (t:t) =
  let y_v = Var (BoolS,y) in    (* BoolSはダミー *)
  substitution (M.singleton x y_v) t


let pa_replace x y ((args,t):pa) =
  (* 引数と変数名がかぶるものは置換しない *)
  if List.mem_assoc x args then
    (args, t)
  else
    let t' = replace x y t in
    (args, t')

let pa2string ((arg,p):pa) =
  let sita,_ = List.fold_left
               (fun (sita,i) (x,s) ->let i_v = Var(s,(Printf.sprintf "_%d" i)) in
                                     (M.add x i_v sita , i+1))
               (M.empty, 0)
               arg
  in
  let p' = substitution sita p in
  p2string p'
       
