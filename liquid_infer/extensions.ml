module List = struct
  include List
        
  let rec insert x i l =
    if i = 0 then
      x::l
    else if i > 0 then
      match l with
      |[] -> raise (Invalid_argument "index out of bounds")
      |y::ys -> y :: (insert x (i-1) ys)
    else
      raise (Invalid_argument "index out of bounds")

  let rec diff l1 l2 =        (* l1\l2 *)
    match l1 with
    |x::xs when List.mem x l2 -> diff xs l2
    |x::xs -> x::(diff xs l2)
    |[] -> []

  let rec uniq = function
  |[] -> []
  |x::xs -> if List.mem x xs then uniq xs else x::(uniq xs)
          
end
            
