val fillsort_to_formula: (Id.t * Type.schema) list -> PreSyntax.measureInfo list -> Formula.t -> Formula.t

val fillsort2formula : Data_info.t M.t -> PreSyntax.measureInfo list -> Formula.t -> Formula.t
val fill_pa_args2type : Data_info.t M.t -> Type.t -> Type.t
val fill_pa_args2schema : Data_info.t M.t  -> Type.schema -> Type.schema

val f: (Id.t * Type.schema) list ->
       PreSyntax.measureInfo list ->
       (Id.t * Type.schema) list ->
       (Id.t * Type.t option TaSyntax.t) list ->
       (Id.t * Type.schema) list
       * (Id.t * Type.schema) list
       * (Id.t * Type.t option TaSyntax.t) list


