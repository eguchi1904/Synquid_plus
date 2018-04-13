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
       

(* synquidに渡せる形式のファイルを出力する 
 input_file :input of synquid_plus*)

let stringof_g_listlist g_listlist =
  (String.concat ""
    (List.map
     (fun (g_name,g_t) ->
       Printf.sprintf
         "%s :: %s\n\n%s = ?? \n\n"
         g_name
         (Type.t2string g_t)
         g_name )
     (List.concat g_listlist)
    )
  )
  
let rec infile_name_to_outfile_name:string -> string =
  (fun file_with_extension ->
    let i = String.rindex file_with_extension '.' in
    let file = String.sub file_with_extension 0 i in
    String.concat "" [file; "_2sq.sq"])


(* mainが推論した結果を、inputファイルに付け足した、ファイルを作成 *)
let output2file input_file (g_listlist,_,_) =
  let output_file = infile_name_to_outfile_name input_file in
  let inchan = open_in input_file in
  let outchan = open_out  output_file in
  (Printf.printf "Open %s!\n" output_file);
  (Printf.fprintf outchan "%s" (stringof_g_listlist g_listlist) ); (* 補助関数情報書き込み *)
  (* 以下で、入力ファイルを書き込み *)
  (try while true do
         (Printf.fprintf outchan "%s\n" (input_line inchan))
       done
   with End_of_file -> close_in inchan);
  close_out outchan
  
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
