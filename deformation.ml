(* 式変形 *)
open Formula


let rec expand = function       (* とりあえず集合演算を展開 *)
  |Intersect ((Union (e1, e2)), e3) |Intersect (e3, (Union (e1, e2))) ->
    let new_e1 = Intersect (e1,e3) in
    let new_e2 = Intersect (e2,e3) in
    let new_e1' = expand new_e1 in
    let new_e2' =  expand new_e2 in
    Union (new_e1', new_e2')
  |Diff ((Union (e1, e2)), e3) ->
    let new_e1 = Diff (e1,e3) in
    let new_e2 = Diff (e2,e3) in
    let new_e1' = expand new_e1 in
    let new_e2' =  expand new_e2 in
    
    Union (new_e1', new_e2')
  (* no recursion *)
  |Bool _|Int _ |Var _ |Unknown _ as e-> e
  (* simple recursion *)
  |Set (s,es) -> Set (s, List.map expand es)
  |Cons (s, v, es) -> Cons (s, v, List.map expand es)
  |UF (s, v, es) -> UF (s, v, List.map expand es)                    
  |If (e1, e2, e3) -> If (expand e1, expand e2, expand e3)
  |Times (e1, e2) -> Times (expand e1, expand e2)
  |Plus (e1, e2) -> Plus (expand e1, expand e2)
  |Minus (e1, e2) -> Minus (expand e1, expand e2)
  |Eq (e1, e2) -> Eq (expand e1, expand e2)
  |Neq(e1, e2) -> Neq(expand e1, expand e2)
  |Lt (e1, e2) -> Lt (expand e1, expand e2)
  |Le (e1, e2) -> Le (expand e1, expand e2)
  |Gt (e1, e2) -> Gt (expand e1, expand e2)
  |Ge (e1, e2) -> Ge (expand e1, expand e2)
  |And (e1, e2) -> And (expand e1, expand e2)
  |Or (e1, e2) -> Or (expand e1, expand e2)
  |Implies (e1, e2) -> Implies (expand e1, expand e2)
  |Iff (e1, e2) -> Iff (expand e1, expand e2)
  |Union (e1, e2) -> Union (expand e1, expand e2)
  |Intersect (e1, e2) -> Intersect (expand e1, expand e2)
  |Diff (e1, e2) -> Diff (expand e1, expand e2)
  |Member (e1, e2) -> Member (expand e1, expand e2)
  |Subset (e1, e2) -> Subset (expand e1, expand e2)
  |Neg e1 -> Neg (expand e1)
  |Not e1 -> Not (expand e1)

  |All _ |Exist _ -> assert false
