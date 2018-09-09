type t

val formula_to_qualifier: Formula.t -> t
val gen_p_candidate: Formula.subst -> (Id.t * Formula.sort) list -> t -> Formula.t list

val refine_qualifiers: Formula.subst -> t list -> t list 
  
