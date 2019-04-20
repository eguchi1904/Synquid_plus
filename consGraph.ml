module Liq = Type                     
   
(* constraintとunknown predicate　からなるグラフ構造 *)
module G:
sig
  
  type cLavel = private int
                      
  val int_of_cLavel: cLavel -> int
    
  type pLavel = private int

  val int_of_pLavel: pLavel -> int

  val def_pLavel: pLavel


  type cNode = {lavel:int
               ;value:Constraint.simple_cons
               ;pos:pLavel list 
               ;neg:pLavel list}

  type pNode = {lavel:int
               ;value:Id.t
               ;isUpp: bool
               ;env:Liq.env
               ;senv:Formula.Senv.t
               ;pos: cLavel list
               ;neg: cLavel list
               }

  type t = {cTable: cNode array; cNodeNum: int;
            pTable: pNode array; pNodeNum: int;
            pIdHash: (Id.t, pLavel) Hashtbl.t
           }

  val log: t -> unit

  val create: S.t -> Constraint.simple_cons list -> t

  val iter_p: (pLavel -> unit) -> t -> unit

  val fold_c: (cLavel -> 'a -> 'a) -> t -> 'a -> 'a

  val fold_p: (pLavel -> 'a -> 'a) -> t -> 'a -> 'a
         
  val pNode_num: t -> int
    
  val cNode_num: t -> int    
    
  val pLavel_of_id: t -> Id.t -> pLavel

  val id_of_pLavel: t -> pLavel -> Id.t

  val id_of_int: t -> int -> Id.t    

  val cons_of_cLavel: t -> cLavel -> Constraint.simple_cons

  val pos_ps: t -> cLavel -> pLavel list

  val neg_ps: t -> cLavel ->pLavel list
    
  val pos_cs: t -> pLavel -> cLavel list
    
  val neg_cs: t -> pLavel -> cLavel list

  val get_p_env: t -> pLavel -> Liq.env

  val is_upp_p: t -> pLavel -> bool

    
end = struct
         
  type cLavel = int

  let int_of_cLavel x = x
              
  type pLavel = int

  let int_of_pLavel x = x
                      
  let def_pLavel = 0
              

  type cNode = {lavel:int
               ;value:Constraint.simple_cons
               ;pos:pLavel list
               ;neg:pLavel list}

  type pNode = {lavel:int
               ;value:Id.t
               ;isUpp: bool               
               ;env: Liq.env
               ;senv:Formula.Senv.t               
               ;pos: cLavel list
               ;neg: cLavel list
               }

  type t = {cTable: cNode array; cNodeNum: int;
            pTable: pNode array; pNodeNum: int
            ;pIdHash: (Id.t, pLavel) Hashtbl.t
           }


  let iter_p f t =
    for p = 0 to t.pNodeNum - 1 do
      f p
    done

  let fold_p f t seed =
    let acc = ref seed in
    let () = for p = 0 to t.pNodeNum - 1 do
               acc:= f p !acc
             done
    in
    !acc

  let fold_c f t seed =
    let acc = ref seed in
    let () = for c = 0 to t.cNodeNum - 1 do
               acc := f c !acc
             done
    in
    !acc
    
  let pLavel_of_id t id =
    try Hashtbl.find t.pIdHash id with
      Not_found -> invalid_arg "pLavel_of_id: invalid id"

  let id_of_pLavel t p =
    try t.pTable.(p).value with
      _ ->  invalid_arg "invalid lavel"

  let id_of_int = id_of_pLavel

  let cons_of_cLavel t c =
    try t.cTable.(c).value with
      _ -> invalid_arg "invalid lavel"
    
    
  let string_of_c_value c_table =
    let _, str = Array.fold_left
                   (fun (i,acc_str) (cnode:cNode) ->
                     let const_str = Constraint.scons2string cnode.value in
                     let str = Printf.sprintf "\n\n\n%d -> \n%s" i const_str in
                     (i+1, acc_str^str))
                   (0, "")
                   c_table
    in
    str

  let string_of_dependency_p t =
    fold_p
      (fun p acc_str ->
        let pos_cs = t.pTable.(p).pos in
        let neg_cs = t.pTable.(p).neg in
        let pos_cs_str = pos_cs
                         |> List.map string_of_int
                         |> String.concat ","
        in
        let neg_cs_str = neg_cs
                         |> List.map string_of_int
                         |> String.concat ","
        in
        let str = Printf.sprintf
                    "\n%s -pos->[%s]; -neg->[%s]"
                    (id_of_pLavel t p)
                    pos_cs_str
                    neg_cs_str
        in
        acc_str^str)
    t
    ""

  let string_of_dependency_c t =
    fold_c
      (fun c acc_str ->
        let pos_ps = t.cTable.(c).pos in
        let neg_ps = t.cTable.(c).neg in
        let pos_ps_str = pos_ps
                         |> List.map (id_of_pLavel t)                       
                         |> String.concat ","
        in
        let neg_ps_str = neg_ps
                         |> List.map (id_of_pLavel t)
                         |> String.concat ","
        in
        let str = Printf.sprintf
                    "\n%d -pos->[%s]; -neg->[%s]"
                    c
                    pos_ps_str
                    neg_ps_str
        in
        acc_str^str)
    t
    ""        
            
  let string_of_id_pLavle t =
    Hashtbl.fold
      (fun p_id pLavel acc_str ->
        ("\n" ^ p_id ^ "->" ^ (string_of_int pLavel) ^ acc_str))
      t.pIdHash
    ""
        
    
  let to_string t =
    "dependency of predicate\n--------------------------------------------------\n"
    ^(string_of_dependency_p t)
    ^"\n"
    ^"dependency of constraint\n--------------------------------------------------"
    ^(string_of_dependency_c t)
    ^"\n\n\n"
    ^" [cLavel<----> constraint] map\n"
    ^(string_of_c_value t.cTable)
    ^ "[pLavel<----> p_id] map\n"
    ^(string_of_id_pLavle t)
    

  let log_och = open_out "graph.log"
              
  let log t =
    Printf.fprintf
      log_och
    "Graph:\n constraint table\n==================================================\n%s"
      (to_string t)
    


  let pNode_num t = t.pNodeNum
                  
  let cNode_num t = t.cNodeNum
                  
         
  let pos_ps graph c_lav =
    graph.cTable.(c_lav).pos

  let neg_ps graph c_lav =
    graph.cTable.(c_lav).neg

  let pos_cs graph p =
    graph.pTable.(p).pos

  let neg_cs graph p =
    graph.pTable.(p).neg

  let get_p_env graph p =
    graph.pTable.(p).env

  let is_upp_p t p =
    t.pTable.(p).isUpp



  module Constructor = struct
    let plav_count = ref 0

    let clav_count = ref 0

    let add_p_hash p_hash p = 
      if Hashtbl.mem p_hash p then
        ()
      else
        let () = Hashtbl.add p_hash p !plav_count in
        incr plav_count

    let add_c_array c_array c =
      let c_lav = !clav_count in
      (c_array.(c_lav) <- c);
      (incr clav_count);
      c_lav
      
    type 'a adj_map = {pos: ('a list) array; neg: ('a list) array}

    let create_adj_map n =
      {pos = Array.make n []; neg = Array.make n [] }

    let add_pos adj_map k v =
      let l = adj_map.pos.(k) in
      if not (List.mem v l) then
        adj_map.pos.(k) <- (v::l)

    let add_neg adj_map k v =
      let l = adj_map.neg.(k) in
      if not (List.mem v l) then      
        adj_map.neg.(k) <- (v::l)
      
    let add_p_map p_hash p_map c_lav pos_ps neg_ps othere_ps =
        let () = S.iter
                   (fun p ->
                     let p_lav = Hashtbl.find p_hash p in
                     add_pos p_map p_lav c_lav)
                   pos_ps
        in
        let () = S.iter
                   (fun p ->
                     let p_lav = Hashtbl.find p_hash p in
                     add_neg p_map p_lav c_lav)
                   neg_ps
        in
        let () = S.iter
               (fun p ->
                 let p_lav = Hashtbl.find p_hash p in
                 (add_neg p_map p_lav c_lav);
                 (add_pos p_map p_lav c_lav))
               othere_ps
        in
        ()
        
    let add_c_map p_hash c_map c_lav pos_ps neg_ps othere_ps =
        let () = S.iter
                   (fun p ->
                     let p_lav = Hashtbl.find p_hash p in
                     add_pos c_map c_lav p_lav)
                   pos_ps
        in
        let () = S.iter
                   (fun p ->
                     let p_lav = Hashtbl.find p_hash p in
                     add_neg c_map c_lav p_lav)
                   neg_ps
        in
        let () = S.iter
               (fun p ->
                 let p_lav = Hashtbl.find p_hash p in
                 (add_neg c_map c_lav p_lav);
                 (add_pos c_map c_lav p_lav))
               othere_ps
        in
        ()        
      
    (* p_map, c_mapを作成 *)
    let rec scan_sub_cs p_hash c_array (p_map:pLavel adj_map) c_map  =function
      |(Constraint.SSub _) as c::other ->
        let pos_ps, neg_ps, othere_ps =
          Constraint.positive_negative_unknown_p c
        in
        let pos_ps_list = S.elements pos_ps in
        let neg_ps_list = S.elements neg_ps in
        let othere_ps_list = S.elements othere_ps in        
        let c_lav = add_c_array c_array c in
        let () = add_p_map p_hash p_map c_lav pos_ps neg_ps othere_ps in
        let () = add_c_map p_hash c_map c_lav pos_ps neg_ps othere_ps in
        scan_sub_cs p_hash c_array p_map c_map other
        
      |(Constraint.SWF _)::other ->
        scan_sub_cs p_hash c_array p_map c_map other
       
      |[] -> ()

           
    let rec scan_wf_cs p_hash p_env_array p_senv_array = function
      |Constraint.SWF (env, (_, Formula.Unknown (senv,_,_,p)))::other ->
        let p_lav = Hashtbl.find p_hash p in
        (assert (p_env_array.(p_lav) = Liq.env_empty));
        (p_env_array.(p_lav) <- env);
        (p_senv_array.(p_lav) <- senv);
        scan_wf_cs p_hash p_env_array p_senv_array other
      |_ :: other -> scan_wf_cs p_hash p_env_array p_senv_array other
                   
      |[] -> ()

    let rec mk_p_hash p_hash = function
      |Constraint.SWF (env, (senv, Formula.Unknown (_,_,_,p)))::other ->
        (add_p_hash p_hash p);
        mk_p_hash p_hash other
      |_ :: other -> mk_p_hash p_hash other
      |[] -> ()

           
    let dummy_c_node c = {lavel = -1
                         ;value = c
                         ;pos =  []
                         ;neg = [] }

    let mk_c_table c_array c_map =
      let len = Array.length c_array in
      let c_table = Array.make len (dummy_c_node c_array.(0)) in
      let () = Array.iteri
                 (fun c_lav c ->
                   c_table.(c_lav) <- {lavel = c_lav (* これいる？ *)
                                      ;value = c
                                      ;pos = c_map.pos.(c_lav)
                                      ;neg = c_map.neg.(c_lav)})
                 c_array
      in
      c_table

    let dummy_p_node = {lavel = -1
                         ;value = ""
                         ;isUpp = false      
                         ;env = Liq.env_empty
                         ;senv = Formula.Senv.empty
                         ;pos = []
                         ;neg = []
                         }
                       
    let mk_p_table up_ps p_count p_hash p_map p_env_array p_senv_array =
      let p_table = Array.make p_count dummy_p_node in
      let () = Hashtbl.iter
                 (fun p p_lav ->
                   p_table.(p_lav) <- {lavel = p_lav
                                      ;value = p
                                      ;isUpp = S.mem p up_ps
                                      ;env = p_env_array.(p_lav)
                                      ;senv = p_senv_array.(p_lav)
                                      ;pos = p_map.pos.(p_lav)
                                      ;neg = p_map.neg.(p_lav)
                                      }
                 )
                 p_hash
      in
      p_table
        

      
      
    let mk_graph up_ps p_hash c_array p_map c_map p_env_array p_senv_array =
      let c_table = mk_c_table c_array c_map in
      let p_table =
        mk_p_table up_ps (!plav_count) p_hash p_map p_env_array p_senv_array
      in
      {cTable = c_table; cNodeNum = !clav_count
      ;pTable = p_table; pNodeNum = !plav_count
      ;pIdHash = p_hash
      }
      
      
      
                   
    let f up_ps cs =
      let sub_cs, wf_cs = List.partition
                            (function
                             |Constraint.SSub _ -> true
                             |Constraint.SWF _ -> false) cs
      in
      let p_hash = Hashtbl.create 1000 in
      let () = mk_p_hash p_hash cs in
      let p_count = !plav_count in
      let c_count = List.length sub_cs in      
      let c_array = Array.make c_count (List.hd cs) in
      let p_map:pLavel adj_map = create_adj_map p_count in
      let c_map:cLavel adj_map = create_adj_map c_count  in
      (* initialize c_array, p_map, c_map *)
      let () = scan_sub_cs p_hash c_array p_map c_map sub_cs in
      let p_env_array = Array.make p_count Liq.env_empty in
      let p_senv_array = Array.make p_count Formula.Senv.empty in
      (* initialize p_env_array p_senv_array *)
      let () = scan_wf_cs p_hash p_env_array p_senv_array wf_cs in
      mk_graph up_ps p_hash c_array p_map c_map p_env_array p_senv_array
      
    end

  let create = Constructor.f
             
    

end

module PMap =
  Map.Make
    (struct
      type t = G.pLavel
      let compare = compare
    end)

module PSet = struct
 include ( Set.Make
                (struct
                  type t = G.pLavel
                  let compare = compare
                end))
  (* include PS *)

  let of_id_Set graph id_set =
    S.fold
      (fun id acc ->
        add (G.pLavel_of_id graph id) acc)
    id_set
    empty
    
end

module CMap = 
  Map.Make
    (struct
      type t = G.cLavel
      let compare = compare
    end)
  

(* predicateだけからなるグラフ *)
(* \Gamma|- pが、
   \Gamma; p; q -> ... 
   の時　p -neg-> q
   
 *)
module PG = struct
  
  type t = {posTable: (G.pLavel list) array
           ;negTable: (G.pLavel list) array
           }

  let pos_ps t p = t.posTable.(G.int_of_pLavel p)

  let neg_ps t p = t.negTable.(G.int_of_pLavel p)                 
  
end



          
