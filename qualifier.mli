type t

val formula_to_qualifier: Formula.t -> t
val mk_qualifier: Id.t list -> Formula.t -> t
val qualifier_to_formula: t -> (Id.t list * Formula.t)
val qualifier_to_string: t -> string
  
val gen_p_candidate: Formula.subst -> (Id.t * Formula.sort) list -> t -> Formula.t list

val refine_qualifiers: Formula.subst -> t list -> t list 
  
