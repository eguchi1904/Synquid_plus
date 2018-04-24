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
end
            
