type z3_env
   
val mk_z3_env : unit -> z3_env  (* deplicate *)
  
val z3_t : float ref            (* time used by z3 *)
  
val convert : Formula.t -> Z3.Expr.expr * Z3.Sort.sort
  
exception CANT_SOLVE  
  
val is_valid : Z3.Expr.expr -> bool
  
val is_satisfiable : Z3.Expr.expr -> bool
  
val satisfiable_but_not_valid : Z3.Expr.expr -> bool
  
