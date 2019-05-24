open Syntax

(* メインの処理、
（環境、テンプレート、合成する関数のスキーマ）=>
　 補助関数のスキーマlist
 *)
let g :(Data_info.t M.t -> Qualifier.t list ->
        Type.env -> Syntax.t -> Type.schema -> (Id.t * Type.schema) list)  =
  (fun  data_infos qualifiers env tmp (ts,ps,t) ->
    let z3_env = UseZ3.mk_z3_env () in
    let g_list = Step2.f z3_env data_infos qualifiers env tmp (ts,ps,t) in
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
  
let apply_synquid data_infos minfos fundecs auxi_sch_list =
  let auxi_goals = List.map (fun (auxi, _) -> (auxi, Syntax.PHole )) auxi_sch_list in
  Run_synquid.f data_infos minfos (auxi_sch_list@fundecs) auxi_goals

(* 
テンプレートから、道の補助関数に要求される肩を推論し、synquidに投げた結果を返す

input:
f = tmp(unknown auxiliary functions include)

output:
"
auxi_1 = ..
auxi_2 = ..
f = tmp
"
 *)

let tmp_to_str f_name tmp =
  match tmp with
  |TaSyntax.PLet ((x, _),t1, TaSyntax.PE (TaSyntax.PSymbol (y, _)))
       when x = f_name && y = f_name ->
    f_name^" = \n"^(TaSyntax.remove_annotations t1 |> Syntax.syn2string )
   
  |_ -> f_name^" = \n"^(TaSyntax.remove_annotations tmp |> Syntax.syn2string )

let report_auxi_infer_is_done auxi_sch_list =
  let fundecs_str_list = List.map
                           (fun (fname, schm) ->
                             Printf.sprintf "%s::%s" fname (Type.schema2string schm))
                           auxi_sch_list
  in
  let fundecs_str = String.concat "\n\n" fundecs_str_list in
  let str = ("\n\n--------------------------------------------------\n"^
               "finish type inference of auxiliary functions\n"^
                 "--------------------------------------------------\n"^
                   fundecs_str)
  in
  Format.eprintf "%s@." str


let report_runnig_synquid () =
  let str = 
    ("\n--------------------------------------------------\n"^
       "running synquid... \n"^
         "--------------------------------------------------\n")
  in
  Format.eprintf "%s@." str  
  
let auxi_defs_to_str auxi_sch_list =
  let fundecs_str_list = List.map
                           (fun (fname, schm) ->
                             Printf.sprintf "%s::%s" fname (Type.schema2string schm))
                       auxi_sch_list
  in
  String.concat "\n\n" fundecs_str_list 
  
  
let g' data_infos minfos qualifiers cons_env fundecs synthesis_mode (f_name, tmp)
  =
  let fundecs' = until_assoc f_name fundecs in (* 自分は覗く *)
  let init_env = (Type.env_add_schema_list Type.env_empty (cons_env@fundecs')) in
  let (ts,ps,f_ty) as f_sch = List.assoc f_name fundecs in
  let z3_env = UseZ3.mk_z3_env () in  
  match TypeInfer.f_check z3_env data_infos qualifiers init_env tmp f_sch with
  |Ok auxi_ty_list ->
    let auxi_sch_list:(Id.t * Type.schema) list =
      List.map (fun (g,ty) -> (g, (ts,ps,ty))) auxi_ty_list
    in
    let () = report_auxi_infer_is_done auxi_sch_list in
    if not synthesis_mode then
      let auxi_sch_str = auxi_defs_to_str auxi_sch_list in
      (f_name, auxi_sch_str)
    else
    let () = report_runnig_synquid () in
    begin
      match apply_synquid data_infos minfos fundecs' auxi_sch_list with
      |Ok auxi_defs_str ->
        let tmp_str = tmp_to_str f_name tmp in
        f_name, (auxi_defs_str^ tmp_str)
      |Error mes -> invalid_arg mes
    end
  |Error _ -> invalid_arg "check fail: not implimented"
    
    
  

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


let output2file output_file  (data_info_map, minfos, fundecs, defs, synthesized_result) =
  let outchan =
    (match output_file with  |None -> stdout |Some s -> open_out s) in
  let data_info_str = Data_info.data_info_map_2_string data_info_map in
  let minfos_str = PreSyntax.minfo_list_2_string minfos in
  let fundecs_str_list = List.map
                           (fun (fname, schm) ->
                             Printf.sprintf "%s::%s" fname (Type.schema2string schm))
                           fundecs
  in
  let fundecs_str = String.concat "\n\n" fundecs_str_list in
  let defs_str_list = List.map
                        (fun (id, prog) ->
                          Printf.sprintf "%s = %s" id (Syntax.syn2string prog))
                        defs
  in
  let defs_str =String.concat "\n\n" defs_str_list in
  let synthesized_result_str =
    List.fold_right (fun (f, def_str) acc -> def_str^acc) synthesized_result ""
  in
  (Printf.fprintf outchan "%s \n\n%s \n\n%s \n\n%s\n%s"
                  data_info_str
                  minfos_str
                  fundecs_str
                  defs_str
                  synthesized_result_str);
  (* 以下で、入力ファイルを書き込み *)
  close_out outchan


(* let rec_def x t =  (Syntax.PLet (x,t, Syntax.PE (Syntax.PSymbol x))) *)
(* let qualifiers = *)
(*   let open Formula in *)
(*   let valVar = Var (IntS, Id.valueVar_id) in *)
(*   let x_id =  Id.genid "x" in *)
(*   let x = Var (IntS, x_id) in *)
(*   let y_id =  Id.genid "y" in *)
(*   let y = Var (IntS, x_id) in   *)
(*   let qLe = Qualifier.mk_qualifier [x_id; y_id]  (Formula.Le (x, valVar)) in *)
(*   let qNeq = Qualifier.mk_qualifier [x_id; y_id]  (Formula.Neq (x, valVar)) in *)
(*   [qLe] *)


(* ad-hocの塊 *)
let main file (gen_mk_tmp: Data_info.t M.t ->  PreSyntax.measureInfo list ->
               Id.t -> Type.schema -> Syntax.t ) synthesis = 
  let lexbuf = if file = "" then  Lexing.from_channel stdin
               else let inchan = open_in (file) in
                    Lexing.from_channel inchan
  in
  let  (cons_env, minfos, fundecs, defs, q_formulas)  = Parser.toplevel Lexer.main lexbuf in
  (* (List.iter print_string (List.map PreSyntax.minfo2string minfos)); *)
  let cons_env,fundecs, defs = Preprocess.f cons_env minfos fundecs defs in
  let data_info_map = Data_info.mk_data_info cons_env in
  let q_formulas = List.map (Preprocess.fillsort_to_formula (cons_env@fundecs) minfos) q_formulas in
  
  let qualifiers = List.map
                     (fun e ->
                       let fv_e =S.elements (Formula.fv e) in
                       Qualifier.mk_qualifier fv_e e)
                     q_formulas
  in
  let () = Printf.printf "\nqualifier:\n%s\n\n"
                    (String.concat "\n" (List.map Qualifier.qualifier_to_string qualifiers))
  in
  (* 応急手当て、predicateパラメタのsortの整合性合わせ 
   *)
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
  let defs =
    List.map
      (fun (x, ta_syn) ->
        let ta_syn' =
          TaSyntax.access_annotation_t
            (function |None -> None
                      |Some ty -> Some (Data_info.fix_sort_in_pred_param data_info_map ty))
          ta_syn
        in
        (x, ta_syn'))
      defs
  in
  let syn_check_goals, infer_goals = List.partition
                                 (fun (id, _) -> List.mem_assoc id fundecs)
                                 defs
  in
  let syn_goals, check_goal = List.partition
                                (fun (id, prg) -> (TaSyntax.auxi_exist_t prg) || prg = TaSyntax.PHole)
                                syn_check_goals
  in


  (* ************************************************** *)  
  (* synthesith *)
  (* ************************************************** *)  
  (* let mk_tmp = gen_mk_tmp data_info_map minfos in *)
  (* let syn_goals = Mk_tmp.f mk_tmp fundecs syn_goals in  ひとまずtemplateの自動生成は休憩*) 
  let synthesized_result:(Id.t * string) list
    = List.map (g' data_info_map minfos qualifiers cons_env fundecs synthesis) syn_goals
  in
  let init_env = (Type.env_add_schema_list Type.env_empty (cons_env@fundecs)) in
  
  (* ************************************************** *)
  (* liquid type checking *)
  (* ************************************************** *)  
  let id_check_result_list =
    List.map
      (fun (x, t) ->
        let z3_env =  UseZ3.mk_z3_env () in
        let x_ty = Type.env_find init_env x in
        (x, TypeInfer.f_check z3_env data_info_map qualifiers init_env t  x_ty ))
      check_goal
  in
  
  (* ************************************************** *)  
  (* liquid type infer *)
  (* ************************************************** *)  
  let infered_result =
    List.map
      (fun (x, t) ->
        let z3_env =  UseZ3.mk_z3_env () in
        (x, TypeInfer.f z3_env data_info_map qualifiers init_env  t  ))
      infer_goals
  in
  let infered_result_sch =
    List.map (fun (id, ty) -> (id, (Type.mk_mono_schmea ty))) infered_result in
  let infered_goal' = (List.map (fun (x,tasyn) -> (x, TaSyntax.remove_annotations tasyn)) infer_goals) in
  (data_info_map, minfos, infered_result_sch, infered_goal', synthesized_result)


  
let _ =
  let file = ref "" in
  let out_file = ref None in
  let mk_tmp_fun = ref Mk_tmp.fold in
  let synthesis = ref false in
  (Arg.parse
     [("-tmp",
      (Arg.String
         (fun s ->
           match s with
           |"merge" -> mk_tmp_fun := Mk_tmp.merge
           |_ -> mk_tmp_fun := Mk_tmp.fold)
      ),
      "tmplates");
      ("-o",
       (Arg.String
          (fun s -> out_file := Some s)),
       "output file name");
      ("-synthesis",
       (Arg.Unit
          (fun () -> synthesis := true)),
      "synthesize")
      
     ]
     (fun s -> file := s)
     ("synquid+: using z3 version" ^ Z3.Version.full_version ));
  let result = main !file !mk_tmp_fun !synthesis in
  (Printf.printf "z3_time:%f" !UseZ3.z3_t);
  output2file !out_file result

