(* customized version of Set *)
module S =
  Set.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
include S

let of_list l = List.fold_left (fun s e -> add e s) empty l
let is_cross s1 s2 = not (S.is_empty (S.inter s1 s2))
