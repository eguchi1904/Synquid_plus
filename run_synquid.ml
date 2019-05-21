let tmp_sq = "tmp.sq"
           
let run_command tmp_sq  = 
    let in_cha = Unix.open_process_in ("synquid "^tmp_sq) in
    let out_ref = ref "" in
    let () = try
        while true do
          let line = input_line in_cha in
          out_ref := !out_ref ^ line^"\n"
        done
      with End_of_file ->
        close_in in_cha
    in
    let synquid_out = !out_ref in
    synquid_out



let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false  

let is_error str =
  contains str "Error"          (* very very naive *)
  
let parse_synquid_output str =
  if is_error str then
    Error ("synquid error:\n"^str)
  else
    Ok str
    

let f data_info_map minfos fundecs goals =
  let tmp_out = open_out tmp_sq in
  let data_info_str = Data_info.data_info_map_2_string data_info_map in
  let minfos_str = PreSyntax.minfo_list_2_string minfos in
  let fundecs_str_list = List.map
                           (fun (fname, schm) ->
                             Printf.sprintf "%s::%s" fname (Type.schema2string schm))
                           fundecs
  in
  let fundecs_str = String.concat "\n\n" fundecs_str_list in
  let goals_str_list = List.map
                        (fun (id, prog) ->
                          Printf.sprintf "%s = %s" id (Syntax.syn2string prog))
                        goals
  in
  let goals_str =String.concat "\n\n" goals_str_list in
  (* write to temporary file *)
  let () = (Printf.fprintf tmp_out "%s \n\n%s \n\n%s \n\n%s \n"
                           data_info_str
                           minfos_str
                           fundecs_str
                           goals_str)
  in
  let () = close_out tmp_out in
  let synquid_out_str = run_command tmp_sq in
  let defs = parse_synquid_output synquid_out_str in
  defs

(* let test_sq = "../synquid/test/pldi16/List-Delete.sq " *)
(* let _ = *)
(*   let synquid_out = run_command test_sq in *)
(*   match parse_synquid_output synquid_out with *)
(*     |Ok defs -> *)
(*       let defs' = List.map (fun (x,tasyn) -> (x, (TaSyntax.remove_annotations tasyn))) defs in *)
(*       let defs_str_list = List.map *)
(*                             (fun (id, prog) -> *)
(*                               Printf.sprintf "%s = %s" id (Syntax.syn2string prog)) *)
(*                             defs' *)
(*       in *)
(*       let defs_str =String.concat "\n\n" defs_str_list in *)
(*       print_string defs_str *)
(*     |Error _ -> print_string ("Error\n"^synquid_out) *)
              



  


    
