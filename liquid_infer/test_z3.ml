open Z3
open Z3.Arithmetic
open Z3.Symbol
open Z3.Expr
open Z3.Solver
let ctx = mk_context [("trace","true"); ("well_sorted_check","true");("debug_ref_count","true")]
let z3_bool = Boolean.mk_sort ctx
let z3_int = Integer.mk_sort ctx

let _ = 
  let v = Expr.mk_const_s ctx "v"  z3_bool  in
  let x = Expr.mk_const_s ctx "x"  z3_int  in  
  let y = Expr.mk_const_s ctx "y"  z3_int  in
  let p = Boolean.mk_eq ctx v (mk_lt ctx x y) in
  let solver = mk_solver ctx None in
  (Solver.add solver [p]);
  let ret = Solver.check solver [] in
    if ret = UNSATISFIABLE then
      print_string "true"
  else if ret = SATISFIABLE then
      print_string "false"
  else
    Printf.printf "cant solve"
    
      
