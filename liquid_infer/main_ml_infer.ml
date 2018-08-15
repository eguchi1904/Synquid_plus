open Syntax

(* メインの処理、
（環境、テンプレート、合成する関数のスキーマ）=>
　 補助関数のスキーマlist
 *)


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
　tmp:テンプレート（本物）
 *)



(* synquidに渡せる形式のファイルを出力する 
 input_file :input of synquid_plus*)


let rec infile_name_to_outfile_name:string -> string =
  (fun file_with_extension ->
    let i = String.rindex file_with_extension '.' in
    let file = String.sub file_with_extension 0 i in
    String.concat "" [file; "_2sq.sq"])


(* mainが推論した結果を、inputファイルに付け足した、ファイルを作成 *)
(* let output2file input_file (g_listlist,_,_) = *)
(*   let output_file = infile_name_to_outfile_name input_file in *)
(*   let inchan = open_in input_file in *)
(*   let outchan = open_out  output_file in *)
(*   (Printf.fprintf outchan "%s" (stringof_g_listlist g_listlist) ); (\* 補助関数情報書き込み *\) *)
(*   (\* 以下で、入力ファイルを書き込み *\) *)
(*   (try while true do *)
(*          (Printf.fprintf outchan "%s\n" (input_line inchan)) *)
(*        done *)
(*    with End_of_file -> close_in inchan); *)
(*   close_out outchan *)


let output2file input_file  (data_info_map, minfos, fundecs, id_type_list) =
  let output_file = infile_name_to_outfile_name input_file in
  let outchan = open_out  output_file in
  let data_info_str = Data_info.data_info_map_2_string data_info_map in
  let minfos_str = PreSyntax.minfo_list_2_string minfos in
  let fundecs_str_list = List.map
                           (fun (fname, schm) ->
                             Printf.sprintf "%s::%s" fname (Type.schema2string schm))
                           fundecs
  in
  let id_type_str_list = List.map
                           (fun (x, ty) ->
                             Printf.sprintf "%s::%s\n"
                                            x
                                            (Type.t2string ty))
                           id_type_list
  in
  let id_type_list_str = String.concat "\n" id_type_str_list in
  let fundecs_str = String.concat "\n\n" fundecs_str_list in
  (Printf.fprintf outchan "%s \n\n%s \n\n%s \n\n %s\n"
                  data_info_str
                  minfos_str
                  fundecs_str
                  id_type_list_str);
  (* 以下で、入力ファイルを書き込み *)
  close_out outchan

let rec_def x t =  (Syntax.PLet (x,t, Syntax.PE (Syntax.PSymbol x)))

let qualifiers =
  let x = Formula.genUnkownP "x" in
  let y = Formula.genUnkownP "y" in
  [Formula.Neq (x,y);  Formula.Lt (x,y)]

let qualifiers = []
(* todo:expand qualifier を作成する *)
let main file = 
  let lexbuf = if file = "" then  Lexing.from_channel stdin
               else let inchan = open_in (file) in
                    Lexing.from_channel inchan
  in
  let  (cons_env, minfos, fundecs, goals)  = Parser.toplevel Lexer.main lexbuf in
  (* (List.iter print_string (List.map PreSyntax.minfo2string minfos)); *)
  let cons_env,fundecs = Preprocess.f cons_env minfos fundecs in
  let data_info_map = Data_info.mk_data_info cons_env in
  let init_env = ((cons_env@fundecs),[]) in
  let ml_env = Ml.shape_env init_env in
  let id_mltype_list =
    List.map (fun (x, t) -> (x, Ml.infer ml_env (rec_def x t)  ))
             goals
  in
  let id_type_list =
    List.map
      (fun (x, t) ->
        let z3_env =  UseZ3.mk_z3_env () in
        (x, TypeInfer.f z3_env data_info_map qualifiers init_env (rec_def x t)  ))
             goals
  in
  (data_info_map, minfos, fundecs, id_type_list)


  
let _ =
  let file = ref "" in
  let mk_tmp_fun = ref Mk_tmp.fold in
  (Arg.parse
     ["-tmp",
      (Arg.String
         (fun s ->
           match s with
           |"merge" -> mk_tmp_fun := Mk_tmp.merge
           |_ -> mk_tmp_fun := Mk_tmp.fold)
      ),
      "tmplates"
      ]
     (fun s -> file := s)
     "synquid+");
  let result = main !file in
  output2file !file result

