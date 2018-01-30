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

  
(* let match_body = PE (PAppFo *)
(*                        (PAppFo (PAuxi "snoc",PSymbol "x'"), *)
(*                         PAppFo (PSymbol "f", PSymbol "xs'"))) *)
               
(* テスト用 *)
(* let pmatch e cases = PI (PMatch (e,cases)) *)
(* let rec_fun f x e =  PF *)
(*                        (PFix *)
(*                           (f, *)
(*                            (PFun (x,e))))                    *)

(* let tmp = rec_fun "f" "l" *)
(*                   (pmatch (PSymbol "l") *)
(*                   [{constructor="Nil";argNames=[];body = PHole}; *)
(*                    {constructor="Cons";argNames=["x'";"xs'"];body =match_body }]) *)

let rec until_assoc x l =
  match l with
  |(y,_)::left when x = y -> []
  |yp :: left -> yp::(until_assoc x left)
  |[] -> []

let g' env fundecs (f_name, tmp) =
  (print_string (Syntax.syn2string tmp));
  
  let fundecs'  = until_assoc f_name fundecs in
  let env :Type.env = (fundecs'@env , []) in
  let t = List.assoc f_name fundecs in
  let (_,_,t') = t in
  (print_string (Type.t2string_sort t'));
  g env tmp t
       

  
let main file =
  let lexbuf = if file = "" then  Lexing.from_channel stdin
               else let inchan = open_in (file) in
                    Lexing.from_channel inchan
  in
  let  (env, minfos, fundecs, goals)  = Parser.toplevel Lexer.main lexbuf in
  (* (List.iter print_string (List.map PreSyntax.minfo2string minfos)); *)
  let env,fundecs = Preprocess.f env minfos fundecs in
  let g_listlist = List.map (g' env fundecs) goals in
  (g_listlist, fundecs, goals)
  (* (for i=0 to 40 do print_newline () done ); *)
  (* (Printf.printf "RESULT:\n\n"); *)
  (* (List.iter *)
  (*   (fun (g_name,g_t) -> *)
  (*     (Printf.printf "%s :: " g_name); *)
  (*     print_string (Type.t2string g_t); *)
  (*     Printf.printf "\n\n%s = ?? \n\n" g_name) *)
  (*   (List.concat g_listlist)); *)
  (* (List.iter *)
  (*   (fun (f_name, tmp) -> *)
  (*     let f_schema = List.assoc f_name fundecs in *)
  (*     (Printf.printf "%s :: %s\n\n" f_name (Type.schema2string f_schema)); *)
  (*     (Printf.printf "%s = %s" *)
  (*                    f_name *)
  (*                    (Syntax.syn2string tmp)) *)
  (*     ) *)
  (*       goals *)
  (* ); *)
  (* (print_newline ()); *)


(* let _ = *)
(*   let file = ref "" in *)
(*   (Arg.parse *)
(*     [] *)
(*     (fun s -> file := s) *)
(*     "synquid+"); *)
(*   let g_listlist, fundecs, goals = main !file in *)
(*   (\* 以下出力 *\) *)
(*   (for i=0 to 40 do print_newline () done ); *)
(*   (Printf.printf "RESULT:\n\n"); *)
(*   (List.iter *)
(*     (fun (g_name,g_t) -> *)
(*       (Printf.printf "%s :: " g_name); *)
(*       print_string (Type.t2string g_t); *)
(*       Printf.printf "\n\n%s = ?? \n\n" g_name) *)
(*     (List.concat g_listlist)); *)
(*   (List.iter *)
(*     (fun (f_name, tmp) -> *)
(*       let f_schema = List.assoc f_name fundecs in *)
(*       (Printf.printf "%s :: %s\n\n" f_name (Type.schema2string f_schema)); *)
(*       (Printf.printf "%s = %s" *)
(*                      f_name *)
(*                      (Syntax.syn2string tmp)) *)
(*       ) *)
(*         goals *)
(*   ); *)
(*   (print_newline ()); *)
