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
  |PAuxi i -> Some i
  |PAppFo (e1,e2) -> auxi_name e1
