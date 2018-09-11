
val fvar_alpha_convert: Formula.t M.t -> ((Id.t * Type.t) -> Id.t) -> Type.t -> Type.t

val fvar_alpha_convert_sch: Formula.t M.t -> ((Id.t * Type.t) -> Id.t) -> Type.schema -> Type.schema
  
val tvar_alpha_convert: (Id.t -> Id.t) -> Type.t -> Type.t
  
val tvar_alpha_convert_sch: (Id.t -> Id.t) -> Type.schema -> Type.schema

val mk_readable_ty: Type.t -> Type.t
  
val mk_readable_sch: Type.schema -> Type.schema
