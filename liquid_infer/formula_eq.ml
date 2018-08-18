open Formula
let rec f e1 e2 =               (* equality of formula e1 and e2 *)
  match e1,e2 with
  |Plus (a,b), Plus (c,d) |Times (a,b), Times (c,d)
   |Eq (a,b), Eq (c,d) |Neq (a,b), Neq (c,d)
   |Lt (a,b), Gt(d,c) |Le (a,b), Ge(d,c)
   |And (a,b), And(c,d) |Or (a,b), Or (c,d) |Iff (a,b), Iff (c,d)
   |Union (a,b), Union (c,d) |Intersect (a,b), Intersect (c,d) -> (* commutative low  *)
    
    ((f a c)&&(f b d)) || ((f a d)&&(f b c))
  |a,b -> a= b
