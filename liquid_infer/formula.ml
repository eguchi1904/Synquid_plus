open Extensions
(* UFLIA *)
type sort = BoolS | IntS | DataS of Id.t * (sort list) | SetS of sort | AnyS of Id.t
            |UnknownS of Id.t   (* for preprocess *)

(* type unop = Neg | Not *)

type sort_subst = sort M.t
              
(* type binop = *)
(*     Times | Plus | Minus |          (\* Int -> Int -> Int      *\) *)
(*     Eq | Neq |                     (\* a -> a -> Bool *\) *)
(*     Lt | Le | Gt | Ge |            (\* Int -> Int -> Bool *\) *)
(*     And | Or | Implies | Iff |     (\* Bool -> Bool -> Bool *\) *)
(*     Union | Intersect | Diff |     (\* Set -> Set -> Set *\) *)
(*     Member | Subset                (\* Int/Set -> Set -> Bool *\) *)

(* formula -- predicate unknownはなくて良いかも、let C in Tなので *)
type t =
  |Bool of bool
  |Int of int
  |Set of sort * (t list)         (* set literal [1, 2, 3] *)
  |Var of sort * Id.t             (* input variable *)
  |Unknown of sort_subst * subst * Id.t        (* predicate unknown with pending substitution *)
  |Cons of sort * Id.t * (t list) (* datatype constructor *)
  |UF of sort * Id.t * (t list)   (* uninterpreted function *)
  |All of (Id.t * sort) list * t  (* 使わない *)
  |Exist of (Id.t * sort) list * t (* 使わない *)
          
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

type qformula =
  (* foall args.{ [p1&&p2&&...] => p } *)
  |QAll of (Id.t* sort) list * t list * t
  (* exist args.{ [p1&&p2&&...] && p } *)
  |QExist of (Id.t* sort) list * t list
           
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
  |Bool b -> if b = true then "True" else "False"
  | Int i -> string_of_int i
  |Set (_,ts) ->let ts_string = String.concat ", " (List.map p2string ts) in
                Printf.sprintf "[%s]" ts_string
  |Var (_,id) ->Printf.sprintf "%s " id
 |Unknown (_, sita, id)->
    let sita_list = M.bindings sita in
    let sita_str_list = List.map
                          (fun (s, p) -> Printf.sprintf "%s->%s" s (p2string p))
                          sita_list
    in
    if sita_list = [] then
      Printf.sprintf "P[%s]" id
    else
      Printf.sprintf "[%s].P[%s]" (String.concat ";" sita_str_list) id              
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
    Printf.sprintf "(%s * %s)" (p2string t1) (p2string t2)
  |Plus (t1,t2) ->
    Printf.sprintf "(%s + %s)" (p2string t1) (p2string t2)
  |Minus (t1,t2) ->
    Printf.sprintf "(%s - %s)" (p2string t1) (p2string t2)
  |Eq (t1,t2) ->
    Printf.sprintf "(%s == %s)" (p2string t1) (p2string t2)
  |Neq (t1,t2) ->
    Printf.sprintf "(%s!=%s)" (p2string t1) (p2string t2)
  |Lt (t1,t2) ->
    Printf.sprintf "(%s < %s)" (p2string t1) (p2string t2)
  |Le (t1,t2) ->
    Printf.sprintf "(%s <= %s)" (p2string t1) (p2string t2)
  |Gt (t1,t2) ->
    Printf.sprintf "(%s > %s)" (p2string t1) (p2string t2)
  |Ge (t1,t2) ->
    Printf.sprintf "(%s >= %s)" (p2string t1) (p2string t2)
  |And (t1,t2) ->
    Printf.sprintf " %s && %s" (p2string t1) (p2string t2)
  |Or (t1,t2) ->
    Printf.sprintf "%s || %s" (p2string t1) (p2string t2)
  |Implies (t1,t2) ->
    Printf.sprintf "%s ==> %s" (p2string t1) (p2string t2)
  |Iff (t1,t2) ->
    Printf.sprintf "%s <=> %s" (p2string t1) (p2string t2)
  |Union (t1,t2) ->
    Printf.sprintf "(%s + %s)" (p2string t1) (p2string t2)
  |Intersect (t1,t2) ->
    Printf.sprintf "(%s * %s)" (p2string t1) (p2string t2)
  |Diff (t1,t2) ->
    Printf.sprintf "(%s - %s)" (p2string t1) (p2string t2)
  |Member (t1,t2) ->
    Printf.sprintf "(%s in %s)" (p2string t1) (p2string t2)
  |Subset (t1,t2) ->
    Printf.sprintf "(%s <= %s)" (p2string t1) (p2string t2)
  |Neg t ->
    Printf.sprintf "-%s" (p2string t )
  |Not t ->
    Printf.sprintf "!%s" (p2string t )

let rec sort2string = function
  |BoolS -> "Bool"
  |IntS -> "Int"
  |DataS (i,sorts) ->
    Printf.sprintf "%s %s" i (String.concat " " (List.map sort2string sorts))
  |SetS s -> Printf.sprintf "Set %s" (sort2string s)
  |AnyS i -> i
  |UnknownS i -> Printf.sprintf "unknown_%s" i
   
let rec pashape2string ((args,rets):pa_shape) =
  match args with
  |s::left -> Printf.sprintf "%s -> %s"
             (sort2string s)
             (pashape2string (left,rets))
  |[] -> sort2string rets
      
let rec p2string_with_sort = function
  |Bool b -> string_of_bool b | Int i -> string_of_int i
  |Set (s,ts) ->let ts_string = String.concat ", " (List.map p2string_with_sort ts) in
                Printf.sprintf "([%s]:%s)" ts_string (sort2string s)
  |Var (s,id) ->Printf.sprintf "(%s:%s) " id (sort2string s)
  |Unknown (sort_sita, sita, id)->
    let sita_list = M.bindings sita in
    let sita_str_list = List.map
                          (fun (s, p) -> Printf.sprintf "%s->%s" s (p2string_with_sort p))
                          sita_list
    in
    if sita_list = [] then
      Printf.sprintf "P[%s]" id
    else
      Printf.sprintf "[%s].P[%s]" (String.concat ";" sita_str_list) id
  |Cons (s,id,ts)|UF (s,id,ts) ->
    let ts_string = String.concat " " (List.map p2string_with_sort ts) in
    Printf.sprintf "((%s %s):%s)" id ts_string (sort2string s)
  |All (args,t) ->
    Printf.sprintf "All(somearg).\n%s" (p2string_with_sort t)
  |Exist (args,t) ->
    Printf.sprintf "Exist(somearg).\n%s" (p2string_with_sort t)
  |If (t1,t2,t3) ->
    Printf.sprintf "if(%s)then %s else %s" (p2string_with_sort t1) (p2string_with_sort t2) (p2string_with_sort t3)
  |Times (t1,t2) ->
    Printf.sprintf "(%s)*(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Plus (t1,t2) ->
    Printf.sprintf "%s + %s" (p2string_with_sort t1) (p2string_with_sort t2)
  |Minus (t1,t2) ->
    Printf.sprintf "(%s)-(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Eq (t1,t2) ->
    Printf.sprintf "(%s == %s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Neq (t1,t2) ->
    Printf.sprintf "(%s)!=(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Lt (t1,t2) ->
    Printf.sprintf "(%s < %s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Le (t1,t2) ->
    Printf.sprintf "(%s <= %s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Gt (t1,t2) ->
    Printf.sprintf "(%s > %s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Ge (t1,t2) ->
    Printf.sprintf "(%s >= %s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |And (t1,t2) ->
    Printf.sprintf "(%s && %s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Or (t1,t2) ->
    Printf.sprintf "(%s)||(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Implies (t1,t2) ->
    Printf.sprintf "(%s)==>(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Iff (t1,t2) ->
    Printf.sprintf "(%s)<=>(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Union (t1,t2) ->
    Printf.sprintf "(%s)+(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Intersect (t1,t2) ->
    Printf.sprintf "(%s)+(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Diff (t1,t2) ->
    Printf.sprintf "(%s)/(%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Member (t1,t2) ->
    Printf.sprintf "(%s)in %s" (p2string_with_sort t1) (p2string_with_sort t2)
  |Subset (t1,t2) ->
    Printf.sprintf "(%s)<= (%s)" (p2string_with_sort t1) (p2string_with_sort t2)
  |Neg t ->
    Printf.sprintf "-(%s)" (p2string_with_sort t )
  |Not t ->
    Printf.sprintf "!(%s)" (p2string_with_sort t )
   


   
(* 普通の変数の *)
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


let rec fv_include_v = function               (* 自由変数、 *)
  |Var (_,i) -> S.singleton i
  |Bool _ | Int _ |Unknown _ -> S.empty
  |Set (_, ts) |Cons (_,_, ts) |UF (_,_,ts) ->
    List.fold_left (fun acc t -> S.union acc (fv_include_v t)) S.empty ts
  |If (t1,t2,t3) ->S.union (fv_include_v t1) (S.union (fv_include_v t2) (fv_include_v t3) )
  |Times(t1,t2) |Plus(t1,t2) |Minus (t1,t2) |Eq(t1,t2) | Neq(t1,t2)|Lt(t1,t2)
   |Le(t1,t2)|Gt(t1,t2)|Ge(t1,t2)|And(t1,t2)|Or(t1,t2)|Implies(t1,t2)|Iff(t1,t2)
   |Union(t1,t2) |Intersect(t1,t2) |Diff(t1,t2) |Member(t1,t2) |Subset(t1,t2)
   ->S.union (fv_include_v t1) (fv_include_v t2)
  |Neg t1 |Not t1 ->fv_include_v t1
  |All (args,t1) |Exist (args,t1) ->
    S.diff (fv_include_v t1) (S.of_list (List.map fst args))
    

let rec fv_sort' = function               (* 自由変数、sortの情報付き。 *)
  |Var (_,i) when i = Id.valueVar_id -> [] (* _v は自由変数でない *)
  |Var (s,i) -> [(i,s)]
  |Bool _ | Int _ |Unknown _ -> []
  |Set (_, ts) |Cons (_,_, ts) |UF (_,_,ts) ->
    List.fold_left (fun acc t -> acc@(fv_sort' t)) [] ts
  |If (t1,t2,t3) ->(fv_sort' t1)@(fv_sort' t2)@(fv_sort' t3)
  |Times(t1,t2) |Plus(t1,t2) |Minus (t1,t2) |Eq(t1,t2) | Neq(t1,t2)|Lt(t1,t2)
   |Le(t1,t2)|Gt(t1,t2)|Ge(t1,t2)|And(t1,t2)|Or(t1,t2)|Implies(t1,t2)|Iff(t1,t2)
   |Union(t1,t2) |Intersect(t1,t2) |Diff(t1,t2) |Member(t1,t2) |Subset(t1,t2)
   ->(fv_sort' t1)@(fv_sort' t2)
  |Neg t1 |Not t1 ->fv_sort' t1
  |All (args,t1) |Exist (args,t1) ->
    List.filter (fun (x,_) -> List.mem x (List.map fst args))  (fv_sort' t1)
   
let fv_sort e = List.uniq (fv_sort' e)

(* _vも自由変数とみなすversion *)
let rec fv_sort_in_v' = function               (* 自由変数、sortの情報付き。 *)
  |Var (s,i) -> [(i,s)]
  |Bool _ | Int _ |Unknown _ -> []
  |Set (_, ts) |Cons (_,_, ts) |UF (_,_,ts) ->
    List.fold_left (fun acc t -> acc@(fv_sort_in_v' t)) [] ts
  |If (t1,t2,t3) ->(fv_sort_in_v' t1)@(fv_sort_in_v' t2)@(fv_sort_in_v' t3)
  |Times(t1,t2) |Plus(t1,t2) |Minus (t1,t2) |Eq(t1,t2) | Neq(t1,t2)|Lt(t1,t2)
   |Le(t1,t2)|Gt(t1,t2)|Ge(t1,t2)|And(t1,t2)|Or(t1,t2)|Implies(t1,t2)|Iff(t1,t2)
   |Union(t1,t2) |Intersect(t1,t2) |Diff(t1,t2) |Member(t1,t2) |Subset(t1,t2)
   ->(fv_sort_in_v' t1)@(fv_sort_in_v' t2)
  |Neg t1 |Not t1 ->fv_sort_in_v' t1
  |All (args,t1) |Exist (args,t1) ->
    List.filter (fun (x,_) -> List.mem x (List.map fst args))  (fv_sort_in_v' t1)
  
              
let fv_sort_include_v e =  List.uniq (fv_sort_in_v' e)
    
   
(* 普通の変数の *)
let rec extract_unknown_p = function               (* 自由変数、 *)
  |Unknown (_, _, i) -> S.singleton i
  |Bool _ | Int _ |Var _ -> S.empty
  |Set (_, ts) |Cons (_,_, ts) |UF (_,_,ts) ->
    List.fold_left (fun acc t -> S.union acc (extract_unknown_p t)) S.empty ts
  |If (t1,t2,t3) ->S.union (extract_unknown_p t1) (S.union (extract_unknown_p t2) (extract_unknown_p t3) )
  |Times(t1,t2) |Plus(t1,t2) |Minus (t1,t2) |Eq(t1,t2) | Neq(t1,t2)|Lt(t1,t2)
   |Le(t1,t2)|Gt(t1,t2)|Ge(t1,t2)|And(t1,t2)|Or(t1,t2)|Implies(t1,t2)|Iff(t1,t2)
   |Union(t1,t2) |Intersect(t1,t2) |Diff(t1,t2) |Member(t1,t2) |Subset(t1,t2)
   ->S.union (extract_unknown_p t1) (extract_unknown_p t2)
  |Neg t1 |Not t1 ->extract_unknown_p t1
  |All (args,t1) |Exist (args,t1) ->
    S.diff (extract_unknown_p t1) (S.of_list (List.map fst args))
   



let rec and_list (es:t list) =
  match es with
  |[] -> Bool true
  |[e] -> e
  |(Bool true)::es' -> and_list es'
  |e::es' -> And (e, and_list es')

let rec list_and (es:t) =
  match es with
  |And (Bool true, e2) -> list_and e2
  |And (e1, Bool true) -> list_and e1
  |And (e1,e2) -> (list_and e1)@(list_and e2)
  |e -> [e]

  



let genFvar s i = Var (s, (Id.genid i))

(* input: r::a->a->Bool
   output:  \x.\y.r x y *)
let id2pa_shape i ((arg_sorts,rets):pa_shape) :pa =
  let args = List.mapi (fun n s -> (Id.genid (string_of_int n) , s)) arg_sorts in
  let uf_args = List.map (fun (x,s) ->Var(s,x)) args in
  let body = UF (rets, i, uf_args) in
  (args,body)
  

let genUnkownP i = Unknown (M.empty, M.empty, (Id.genid i))
                 
let genUnknownPa ((args,p):pa) s = (args, genUnkownP s) (* for predicate abstraction *)

let genUnknownPa_shape ((arg_sort,rets):pa_shape) s =
  (Id.init_pa_arg_counter ());
  let args = List.fold_right
               (fun  sort args -> args@[((Id.gen_pa_arg ()), sort)])
               arg_sort
               []
  in
  (args, genUnkownP s)


(* -------------------------------------------------- *)
(* sort *)
(* -------------------------------------------------- *)
let rec var_in_sort = function
  |AnyS i -> S.singleton i
  |UnknownS i -> S.singleton i 
  |DataS (i, sortlist) ->
    List.fold_left (fun acc sort -> S.union (var_in_sort sort) acc) S.empty sortlist
  |SetS s -> var_in_sort s
  |BoolS|IntS -> S.empty
  
(* sort中のanyS,unkonwnSに対する代入
  preprocess
  type instantiate 
 で使用。 *)
let rec sort_subst sita = function
  |AnyS i when M.mem i sita -> M.find i sita
  |UnknownS i when M.mem i sita -> M.find i sita
  |DataS (i, sortlist) ->DataS(i, List.map (sort_subst sita) sortlist )
  |SetS s -> SetS (sort_subst sita s)
  | s -> s

let compose_sort_subst (sita1:sort M.t) (sita2:sort M.t) = (* sita t = sita1(sita2 t) *)
  let sita2' = M.mapi
                 (fun i t ->
                   sort_subst sita1 t)
                 sita2         
  in
  M.union (fun i t1 t2 -> Some t2) sita1 sita2'           

let rec sort_subst_to_shape sita ((args, s):pa_shape) :pa_shape=
  (List.map (sort_subst sita) args, sort_subst sita s)
       
let rec sort_subst2formula (sita:sort_subst) = function
  |Bool b -> Bool b
  |Int i -> Int i
  |Unknown (sort_sita, formula_sita, i) ->
    let sort_sita' = compose_sort_subst sita sort_sita in
    let formula_sita' = M.map (sort_subst2formula sita) formula_sita in
    Unknown (sort_sita', formula_sita', i)
  |Set (s, ts) ->
    let ts' = List.map (sort_subst2formula sita) ts in
    Set (sort_subst sita s, ts')
  |Var (s,i) ->Var (sort_subst sita s, i)
  |Cons (s, i, ts) ->
    let ts' = List.map (sort_subst2formula sita) ts in
    Cons (sort_subst sita s, i, ts')
  |UF (s, i, ts) ->
    let ts' = List.map (sort_subst2formula sita) ts in
    UF (sort_subst sita s, i, ts')
                  
  (* 残りはただの再起 *)
  |All (is, t') ->All (is, (sort_subst2formula sita t'))
  |Exist (is, t') ->Exist (is, (sort_subst2formula sita t'))
  |If (t1, t2, t3) ->If ((sort_subst2formula sita t1),
                         (sort_subst2formula sita t2),
                         (sort_subst2formula sita t3))
  |Times (t1, t2) -> Times ((sort_subst2formula sita t1),
                            (sort_subst2formula sita t2))
  |Plus (t1, t2) -> Plus ((sort_subst2formula sita t1),
                          (sort_subst2formula sita t2))
  |Minus (t1, t2) -> Minus ((sort_subst2formula sita t1),
                            (sort_subst2formula sita t2))
  |Eq (t1, t2) -> Eq ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Neq (t1, t2) -> Neq ((sort_subst2formula sita t1),
                        (sort_subst2formula sita t2))
  |Lt (t1, t2) -> Lt ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Le (t1, t2) -> Le ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Gt (t1, t2) -> Gt ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Ge (t1, t2) -> Ge ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |And (t1, t2) -> And ((sort_subst2formula sita t1),
                        (sort_subst2formula sita t2))
  |Or (t1, t2) -> Or ((sort_subst2formula sita t1),
                      (sort_subst2formula sita t2))
  |Implies (t1, t2) -> Implies ((sort_subst2formula sita t1),
                                (sort_subst2formula sita t2))
  |Iff (t1, t2) -> Iff ((sort_subst2formula sita t1),
                        (sort_subst2formula sita t2))
  |Union (t1, t2) -> Union ((sort_subst2formula sita t1),
                            (sort_subst2formula sita t2))
  |Intersect (t1, t2) -> Intersect ((sort_subst2formula sita t1),
                                    (sort_subst2formula sita t2))
  |Diff (t1, t2) -> Diff ((sort_subst2formula sita t1),
                          (sort_subst2formula sita t2))
  |Member (t1, t2) -> Member ((sort_subst2formula sita t1),
                              (sort_subst2formula sita t2))
  |Subset (t1, t2) -> Subset ((sort_subst2formula sita t1),
                              (sort_subst2formula sita t2))
  |Neg t1 -> Neg (sort_subst2formula sita t1)
  |Not t1 -> Not (sort_subst2formula sita t1)
           

let rec sort_anyids = function
  |AnyS i  -> S.singleton i
  |DataS (i, sortlist) ->
    let anyids_list = List.map sort_anyids sortlist in
    List.fold_left (fun acc ids -> S.union acc ids) S.empty anyids_list
  |SetS s -> sort_anyids s
  |BoolS|IntS -> S.empty
  |UnknownS _ -> assert false

(* Any a と Unkown a' で　a != a' *)
(* ソートs中のAny a を　Unknown a' に変換する *)
let rec any2unknownsort s =
  let any_ids = sort_anyids s in
  let sita = S.fold
               (fun any_id sita -> M.add any_id (UnknownS (Id.genid any_id)) sita)
               any_ids
               M.empty
  in
  sort_subst sita s

let rec any2unknownsort_pa (args,rets) =
  let any_args =
    List.fold_left
      (fun acc set -> S.union set acc)
      S.empty
      (List.map sort_anyids args)
  in
  let any_ids = S.union any_args (sort_anyids rets) in
  let sita = S.fold
               (fun any_id sita -> M.add any_id (UnknownS (Id.genid any_id)) sita)
               any_ids
               M.empty
  in
  let args' = List.map (sort_subst sita) args in
  let rets' = sort_subst sita rets in
  (args', rets')
  
  
exception Unify_Err
let rec unify_sort constrain sita =
  match constrain with

  |((UnknownS a), sort2):: c  ->
    let sita' = compose_sort_subst (M.singleton a sort2) sita in
    let c' = List.map           (* 制約全体に代入[sort2/a]c *)
               (fun (c1,c2)-> (sort_subst (M.singleton a sort2) c1,
                               sort_subst (M.singleton a sort2) c2))
               c
    in
    unify_sort c' sita'
    
  |(sort2, (UnknownS a)) :: c ->
    let sita' = compose_sort_subst (M.singleton a sort2) sita in
    let c' = List.map           (* 制約全体に代入[sort2/a]c *)
               (fun (c1,c2)-> (sort_subst (M.singleton a sort2) c1,
                               sort_subst (M.singleton a sort2) c2))
               c
    in
    unify_sort c' sita'
                                                    
  |(DataS (i, sorts1), (DataS (i', sorts2))) :: c  when i = i' ->
    let new_c = (List.map2 (fun a b ->(a,b)) sorts1 sorts2)@c in
    unify_sort new_c sita

  |((SetS s1),(SetS s2)) :: c ->
    let new_c = (s1,s2) :: c in
    unify_sort new_c sita

  |(s1,s2) :: c when s1 = s2 -> unify_sort c sita

  |[] -> sita

  |(s1,s2) :: c ->
    raise Unify_Err


    
      
(* let genUnknownPreAbst i ((arg_s,s):pa_shape) = *)
(*   let args = List.map (fun s ->(Id.genid "ar"),s) arg_s in *)
(*   let unknownP = genUnkownP i in *)
(*   Abs (args,unknownP) *)
let rec subst_compose (sita1:subst) (sita2:subst) = (* sita t = sita1(sita2 t) *)
  M.union (fun i t1 t2 -> Some t2)
          sita1
          (M.mapi (fun i t2 -> substitution sita1 t2) sita2)

and substitution (sita:subst) (t:t) =
  match t with
  |Var (s,i) when (* s = BoolS && *) M.mem i sita ->
    (match M.find i sita with
     |Var (_,i') -> Var (s,i')  (* 代入先のsortを参照する。 *)
     | p -> p)

  |Unknown (sort_sita, sita1, i) when M.mem i sita ->
    let p = M.find i sita in
    (sort_subst2formula sort_sita (substitution sita1 p))        (* pending substitution を展開する。 *)

  |Unknown (sort_sita, sita1, i) ->
    let sita' = subst_compose sita sita1 in
    Unknown (sort_sita, sita', i)          (* pending substitution を合成 *)

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

let substitution_to_pa sita ((args,t):pa) :pa=
  let sita' = M.delete_list sita (List.map fst args) in
  (args, (substitution sita' t))


     
  

let pa2string ((arg,p):pa) =
  let sita,_ = List.fold_left
               (fun (sita,i) (x,s) ->let i_v = Var(s,(Printf.sprintf "_%d" i)) in
                                     (M.add x i_v sita , i+1))
               (M.empty, 0)
               arg
  in
  let p' = substitution sita p in
  p2string p'
       
