 let rec repeat = (fun  f n x ->  if  n =  0 then x else f (repeat f (n -1) x)) in
 let h = (fun x -> if x then false else true) in
 let notnot = repeat h (1 + 1) in
 let h2 = (fun x -> x + 1) in
 let succsucc = repeat h2 (1 + 1) in
 if notnot true then succsucc 0 else 0
