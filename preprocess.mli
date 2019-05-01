val fillsort_to_formula: (Id.t * Type.schema) list -> PreSyntax.measureInfo list -> Formula.t -> Formula.t

val f: (Id.t * Type.schema) list ->
       PreSyntax.measureInfo list ->
       (Id.t * Type.schema) list ->
       (Id.t * Type.t option TaSyntax.t) list ->
       (Id.t * Type.schema) list
       * (Id.t * Type.schema) list
       * (Id.t * Type.t option TaSyntax.t) list
