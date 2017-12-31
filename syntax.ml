type t = PE of e | PI of b | PF of f | PHole
                                 
 and e =                        (* E-term *)
   |PSymbol of Id.t             (* Symbol - variable , constract *)
   |PAuxi of Id.t               (* auxiliary function *)
   |PAppFo of e * e
 (*   |PAppHo of e * f  真面目に型推論器を実装する必要が出てくるので省略？ *)
                                 
 and b =                        (* branching-term *)
   |PIf of e * t * t
   |PMatch of e * (case list)

 and f =
   |PFun of Id.t * t
   |PFix of Id.t * f

 and case = {constructor : Id.t ; argNames : Id.t list ; body : t} 

let rec auxi_exist (e:e) =
  match e with
  |PSymbol _ -> false
  |PAuxi _ -> true
  |PAppFo (e1,e2) ->(auxi_exist e1)||(auxi_exist e2)

let rec auxi_name (e:e) =
  match e with
  |PSymbol _ -> raise (Invalid_argument "auxi_function not found")
  |PAuxi i ->  i
  |PAppFo (e1,e2) -> auxi_name e1

let mk_case a b c = {constructor=a; argNames=b; body=c }

let rec syn2string = function
  |PE e -> syn2string_e e
  |PI b -> syn2string_b b
  |PF f -> syn2string_f f
  |PHole -> "??"

and syn2string_e = function
  |PSymbol i -> i
  |PAuxi i -> i
  |PAppFo (e1,e2) -> Printf.sprintf "%s (%s)" (syn2string_e e1) (syn2string_e e2)

and syn2string_b = function
  |PIf (e,t1,t2) ->
    Printf.sprintf "if %s then \n %s \n else %s \n"
                   (syn2string_e e)
                   (syn2string t1)
                   (syn2string t2)
  |PMatch (e, cases) ->
    Printf.sprintf "match %s with \n %s "
                  (syn2string_e e)
                  (String.concat "\n" (List.map syn2string_case cases))

and syn2string_f = function
  |PFun (x,t) ->
    Printf.sprintf "\\%s.\n%s" x (syn2string t)
  |PFix (x,f) -> syn2string_f f

and syn2string_case {constructor = cons; argNames = xs; body = t} =
  Printf.sprintf "%s %s ->%s" cons (String.concat " " xs) (syn2string t)
   
    
