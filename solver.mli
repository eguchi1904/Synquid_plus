exception InValid of Constraint.simple_cons
exception UnSat of Constraint.simple_cons
                 
val f :    hints: Formula.t list M.t
        -> objective_predicates: Id.t list 
        -> constraints: Constraint.simple_cons list
        -> Formula.t M.t
        
