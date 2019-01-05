
(* customized version of Map *)

module M =
  Map.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
  
include M

let add_list xys env = List.fold_left (fun env (x, y) -> add x y env) env xys
let add_list2 xs ys env = List.fold_left2 (fun env x y -> add x y env) env xs ys
let delete_list map xs =
  M.filter (fun key _ -> not (List.mem key xs)) map
  
let add_list_map key elm (map: ('a list) t) =
  if M.mem key map then
    (M.add key (elm :: (M.find key map)) map)
  else
    M.add key [elm] map


let find_defo key defo m =
  match M.find_opt key m with
  |Some v -> v
  |None -> defo
  
