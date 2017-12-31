open Syntax
   
let g env tmp t =
  let z3_env = UseZ3.mk_z3_env () in
  let g_list = Step2.f env tmp t z3_env in
  let g_ans_list =  List.map
                     (fun (g_name,g_env,g_t) ->
                       (g_name, Step3.f g_name g_env g_t))
                     g_list
  in
  g_ans_list

  
let match_body = PE (PAppFo
                       (PAppFo (PAuxi "snoc",PSymbol "x'"),
                        PAppFo (PSymbol "f", PSymbol "xs'")))
                    

               
                             

        

(* テスト用 *)
let pmatch e cases = PI (PMatch (e,cases))
let rec_fun f x e =  PF
                       (PFix
                          (f,
                           (PFun (x,e))))                   

let tmp = rec_fun "f" "l"
                  (pmatch (PSymbol "l")
                  [{constructor="Nil";argNames=[];body = PHole};
                   {constructor="Cons";argNames=["x'";"xs'"];body =match_body }])

let rec until_assoc x l =
  match l with
  |(y,_)::left when x = y -> []
  |yp :: left -> yp::(until_assoc x left)
  |[] -> []

let g' env fundecs tmp f_name =
  let fundecs'  = until_assoc f_name fundecs in
  let env :Type.env = (fundecs'@env , []) in
  let t = List.assoc f_name fundecs in
  g env tmp t
       
let _ =
  let lexbuf = Lexing.from_channel stdin in
  let  (env, minfos, fundecs, l)  = Parser.toplevel Lexer.main lexbuf in
  let env,fundecs = Preprocess.f env minfos fundecs in
  let g_listlist = List.map (g' env fundecs tmp) l in
  List.iter
    (fun (g_name,g_t) ->
      (Printf.printf "auxi:%s\n" g_name);
      print_string (Type.t2string g_t);
      Printf.printf "\n\n\n")
    (List.concat g_listlist)

