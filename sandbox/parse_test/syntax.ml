type ty =
 |Int|Bool|TFun of ty * ty |Data  of string * (ty list)

type env = (string * ty) list


let rec ty2string = function
  |Int ->  "Int"
  |Bool -> "Bool"
  |TFun (t1,t2) -> Printf.sprintf "(%s)->%s" (ty2string t1) (ty2string t2)
  |Data (i, ts) -> Printf.sprintf "%s %s" i
                                (String.concat " " (List.map ty2string ts))

let rec env2string = function
  |(x,t)::env' -> Printf.sprintf "%s :: %s\n%s" x (ty2string t) (env2string env')
  |[] -> "------------------------------------------------------------"
          
let f a b = match a with
    (env,fundecs,l) -> (b@env, fundecs, l)
