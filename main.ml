open Syntax

(* メインの処理、
（環境、テンプレート、合成する関数のスキーマ）=>
　 補助関数のスキーマlist
 *)
let g :(Type.env -> Syntax.t -> Type.schema -> (Id.t * Type.schema) list)  =
  (fun env tmp (ts,ps,t) ->
    let z3_env = UseZ3.mk_z3_env () in
    let g_list = Step2.f env tmp (ts,ps,t) z3_env in
    let g_ans_list =  List.map
                        (fun (g_name,g_env,g_t) ->
                          let closed_g_t =  Step3.f g_name g_env g_t in
                          (g_name,(ts, ps, closed_g_t) ))
                        g_list
    in
    g_ans_list)



let rec until_assoc x l =
  match l with
  |(y,_)::left when x = y -> []
  |yp :: left -> yp::(until_assoc x left)
  |[] -> []

let mk_data_cons_list :((Id.t * Type.schema) list ->  ((Id.t * Type.schema) list) M.t)
  = (fun env ->
    let rec which_data_cons  = function
      |Type.TScalar (Type.TData (i,_,_), _) -> i
      |Type.TFun (_,t) -> which_data_cons t
      |_ -> assert false
    in
    let rec mk_data_cons_list' env ans =
      match env with
      |(cons,(ts,ps,t) ):: left ->
        let data_type_id  = which_data_cons t in
        mk_data_cons_list' left (List_map.add data_type_id (cons, (ts,ps,t)) ans)
      |[] -> ans
    in
    mk_data_cons_list' env M.empty)

  
(* env:コンストラクタの型環境
　fundecs: 補助関数の型
　f_name: 合成目標の関数名
　tmp:仮のテンプレート
 *)
  
let g' env fundecs (f_name, tmp) = (* envにはコンストラクタの情報 *)
  (print_string (Syntax.syn2string tmp));
  (Printf.printf "env\n%s" (Type.env2string (env,[])));
  let data_cons_list = mk_data_cons_list env in (* データ型とコンストラクタの対応 *)
  let fundecs'  = until_assoc f_name fundecs in
  let env :Type.env = (fundecs'@env , []) in
  let t = List.assoc f_name fundecs in
  let tmp = Mk_tmp.fold f_name t tmp data_cons_list in
  (Printf.fprintf stderr
                  "%s :: %s\n"
                  f_name
                  (Type.schema2string t));
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
                        (Type.schema2string g_t)
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


let _ =
  let file = ref "" in 
  (Arg.parse
     []
     (fun s -> file := s)
     "synquid+");
  let result = main !file in
  output2file !file result

