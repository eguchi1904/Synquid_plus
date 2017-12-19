type t  =(Id.t * Type.schema) list * (Formula.t list)

let find env v =
  match env with
    (l , p) -> List.assoc v l

             
