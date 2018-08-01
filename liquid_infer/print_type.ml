open Type

let rec t2string = function
  |TScalar (b,p) ->Printf.sprintf "{%s | p}" (b2string b)
  |TFun ((x,t1),t2) -> Printf.sprintf "%s:%s ->\n %s" x (t2string t1) (t2string t2)
  |TAny a ->Printf.sprintf "%s" a
  |TBot -> "Bot"

and b2string = function
  |TBool ->"Bool"|TInt -> "Int"
  |TData (i,ts,ps) ->
    let ts_string = List.map t2string ts in
    Printf.sprintf "D%s %s" i (String.concat " " ts_string)
  |TVar x -> Printf.sprintf "Var(%s)" x
  
