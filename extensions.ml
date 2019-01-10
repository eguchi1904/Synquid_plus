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

  let rec uniq_f (eq:'a -> 'a -> bool) (l:'a list) =
    match l with
    |x::xs when List.exists (eq x) xs -> uniq_f eq xs
    |x::xs -> x::(uniq_f eq xs)
    |[] -> []

  (* output  (len l2)^(len l1) *)
  let rec enumerate_table (key_list:'a list)
                    (var_list:'b list)
          :('a * 'b) list list = match key_list with
    |key::xs ->
      let key_v_list = List.map (fun var -> (key, var)) var_list  in
      let xs_table_list = enumerate_table xs var_list in
      List.concat
        (List.map
           (fun (key, var) -> List.map (fun table -> (key, var)::table) xs_table_list)
           key_v_list)
    |[] -> []


  let flatten_opt_list l =
    l|> List.filter (function Some _  -> true | None -> false)
     |> List.map (function Some s -> s | None -> assert false)
          
      
    
          
end
            
