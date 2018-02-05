open Main
let sq_files = ["./sq_files/fold-sort.sq";
                "./sq_files/list-rev.sq";
                "./sq_files/uniq_list.sq" ;
                "./sq_files/concat.sq";
                "./sq_files/bin2list.sq";
                "./sq_files/partition.sq";
                "./sq_files/merge_sort.sq";
                "./sq_files/quick_sort.sq"
               ]

let print_result (g_listlist, fundecs, goals) =
  (List.iter
     (fun (g_name,g_t) ->
       (Printf.printf "%s :: " g_name);
       print_string (Type.t2string g_t);
       Printf.printf "\n\n%s = ?? \n\n" g_name)
     (List.concat g_listlist));
  (List.iter
     (fun (f_name, tmp) ->
       let f_schema = List.assoc f_name fundecs in
       (Printf.printf "%s :: %s\n\n" f_name (Type.schema2string f_schema));
       (Printf.printf "%s = %s"
                      f_name
                      (Syntax.syn2string tmp))
     )
     goals)
  
let _ =
  let file = ref "" in 
  (Arg.parse
     []
     (fun s -> file := s)
     "synquid+");
  if !file <> "" then
    (* 入力ファイルを実行 *)
    let result = main !file in
    (for i=0 to 40 do print_newline () done );
    print_result result
  else
    (* テスト実行 *)
    let results = List.map
                    (fun file -> let st = Sys.time () in
                                 let result = main file in
                                 let time = (Sys.time () ) -. st in
                                 (file,time, result))
                    sq_files
    in
    (for i=0 to 40 do print_newline () done );  
    (List.iter
       (fun (filename, time, result) ->
         (Printf.printf "RESULT:%s\nTime:%f\n" filename time);
         (print_result result);
         Printf.printf "\n\n\n\n\n"))
      results
    
    
