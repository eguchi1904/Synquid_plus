type 'a t = ('a list) M.t

let add : (Id.t -> 'a -> 'a t -> 'a t) =
  (fun key v map ->
    (try let list = M.find key map in
         M.add key (v::list) map
     with
     |Not_found -> M.add key [v] map)
  )
