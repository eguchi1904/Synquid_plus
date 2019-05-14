open Formula
let rec f e1 e2 =               (* equality of formula e1 and e2 *)
  match e1,e2 with
 (* commutative bin  *)    
  |Plus (a,b), Plus (c,d) |Times (a,b), Times (c,d)
   |Eq (a,b), Eq (c,d) |Neq (a,b), Neq (c,d)
   |Lt (a,b), Gt(d,c) |Le (a,b), Ge(d,c)
   |And (a,b), And(c,d) |Or (a,b), Or (c,d) |Iff (a,b), Iff (c,d)
   |Union (a,b), Union (c,d) |Intersect (a,b), Intersect (c,d) ->
    
    ((f a c)&&(f b d)) || ((f a d)&&(f b c))
 (* non commutative bin  *)       
  |Minus(t1,t2), Minus(t1', t2') |Lt(t1,t2), Lt(t1',t2') |Le(t1,t2), Le(t1',t2')
   |Gt(t1,t2), Gt(t1',t2') |Ge(t1,t2), Ge(t1',t2') |Implies(t1,t2), Implies(t1',t2')
   |Diff(t1,t2), Diff(t1',t2')|Member(t1,t2), Member(t1',t2')|Subset(t1,t2),Subset(t1',t2') ->
    (f t1 t1')&&(f t2 t2')
   
  |If (t1,t2,t3), If (t1',t2',t3') ->
    (f t1 t1')&&(f t2 t2')&&(f t3 t3')

  |Neg t1, Neg t2 |Not t1, Not t2 ->  f t1 t2   
  |Set (s1, t1_list), Set (s2, t2_list) ->
    (s1 = s2)
    &&(List.for_all2 (fun t1 t2 -> f t1 t2) t1_list t2_list)
   
  |Cons (s1, name1, t1_list),Cons (s2, name2, t2_list)
  |UF (s1, name1, t1_list),UF (s2, name2, t2_list) ->    
    (name1 = name2)
    &&(s1 = s2)
    &&(List.for_all2 (fun t1 t2 -> f t1 t2) t1_list t2_list)   

  |Bool _, Bool _ |Int _, Int _ |Var _, Var _  -> e1 = e2
  (* unknown predicate *)
  |Unknown (senv1, sort_sita1, sita1, p1),
   Unknown (senv2, sort_sita2, sita2, p2) ->
    (* do not compare senv *)
    if p1 = p2 then
      let () = assert (senv1 = senv2) in
      (M.equal f sita1 sita2)
      &&(M.equal (=) sort_sita1 sort_sita2)
    else
      false

  |a, b ->
    let () = assert (a <> b) in false
    
