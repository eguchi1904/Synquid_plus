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
　tmp:テンプレート（本物）
 *)

  
  let g' cons_env fundecs  (f_name, tmp) :(Id.t * Syntax.t * ((Id.t * Type.schema) list))
  = (* cons_envにはコンストラクタの情報 *)
  (print_string (Syntax.syn2string tmp));
  (Printf.printf "cons_env\n%s" (Type.env2string (cons_env,[])));
  let fundecs'  = until_assoc f_name fundecs in
  let env :Type.env = (fundecs'@cons_env , []) in
  let t = List.assoc f_name fundecs in
  (Printf.fprintf stderr
                  "%s :: %s\n"
                  f_name
                  (Type.schema2string t));
  f_name, tmp, (g env tmp t)
  

(* synquidに渡せる形式のファイルを出力する 
 input_file :input of synquid_plus*)

let stringof_g_listlist (f_name, tmp, g_listlist) =
  let g_types = 
  (String.concat ""
                 (List.map
                    (fun (g_name,g_t) ->
                      Printf.sprintf
                        "%s :: %s\n\n%s = ?? \n\n"
                        g_name
                        (Type.schema2string g_t)
                        g_name )
                     g_listlist
                 )
  )
  in
  let f_tmp =
    Printf.sprintf "%s = %s" f_name (Syntax.syn2string tmp)
  in
  Printf.sprintf "%s\n\n%s" g_types f_tmp


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


let output2file input_file  (data_info_map, minfos, fundecs, goals) =
  let output_file = infile_name_to_outfile_name input_file in
  let outchan = open_out  output_file in
  let data_info_str = Data_info.data_info_map_2_string data_info_map in
  let minfos_str = PreSyntax.minfo_list_2_string minfos in
  let fundecs_str_list = List.map
                           (fun (fname, schm) ->
                             Printf.sprintf "%s::%s" fname (Type.schema2string schm))
                           fundecs
  in
  let fundecs_str = String.concat "\n\n" fundecs_str_list in
  (Printf.fprintf outchan "%s \n\n%s \n\n%s \n\n \n"
                  data_info_str
                  minfos_str
                  fundecs_str);
  (* 以下で、入力ファイルを書き込み *)
  close_out outchan

let rec_def x t =  (Syntax.PLet (x,t, Syntax.PE (Syntax.PSymbol x)))
let qualifiers =
  let open Formula in
  let valVar = Var (IntS, Id.valueVar_id) in
  let x_id =  Id.genid "x" in
  let x = Var (IntS, x_id) in
  let qLe = Qualifier.mk_qualifier [x_id]  (Formula.Le (x, valVar)) in
  let qGe = Qualifier.mk_qualifier [x_id]  (Formula.Ge (x, valVar)) in
    [qLe; qLe]


let main file (gen_mk_tmp: Data_info.t M.t ->  PreSyntax.measureInfo list ->
               Id.t -> Type.schema -> Syntax.t ) = 
  let lexbuf = if file = "" then  Lexing.from_channel stdin
               else let inchan = open_in (file) in
                    Lexing.from_channel inchan
  in
  let  (cons_env, minfos, fundecs, defs)  = Parser.toplevel Lexer.main lexbuf in
  (* (List.iter print_string (List.map PreSyntax.minfo2string minfos)); *)
  let cons_env,fundecs = Preprocess.f cons_env minfos fundecs in
  let data_info_map = Data_info.mk_data_info cons_env in
  (* 応急手当て、predicateパラメタのsortの整合性合わせ*)
  let cons_env =
    List.map
      (fun (id, sch) ->
        (id, Data_info.fix_sort_in_pred_param_schema data_info_map sch))
      cons_env
  in
  let fundecs =
    List.map
      (fun (id, sch) ->
        (id, Data_info.fix_sort_in_pred_param_schema data_info_map sch))
      fundecs
  in


  let syn_goals, infer_goals = List.partition
                                 (fun (id, _) -> List.mem_assoc id fundecs)
                                 defs
  in
  (* synthesith *)
  let mk_tmp = gen_mk_tmp data_info_map minfos in
  let syn_goals = Mk_tmp.f mk_tmp fundecs syn_goals in (* 各ゴールにtemplateを設定 *)
  let f_tmp_g_list:(Id.t * Syntax.t * ((Id.t * Type.schema) list)) list
    = List.map (g' cons_env fundecs) syn_goals
  in
  let new_fundecs = List.fold_left
                   (fun acc (id, t, auxi_defs) ->
                     acc@auxi_defs)
                   fundecs
                   f_tmp_g_list
  in
  (* liquid type infer *)
  let init_env = ((cons_env@fundecs),[]) in
  let id_type_list =
    List.map
      (fun (x, t) ->
        let z3_env =  UseZ3.mk_z3_env () in
        (x, TypeInfer.f z3_env data_info_map qualifiers init_env (rec_def x t)  ))
      infer_goals
  in
  let id_sch_list = List.map (fun (id, ty) -> (id, (([],[],ty):Type.schema))) id_type_list in
  let new_fundecs = new_fundecs@id_sch_list in
  (data_info_map, minfos, new_fundecs, defs)


  
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
  let result = main !file !mk_tmp_fun in
  output2file !file result

