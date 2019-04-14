module Liq = Type                     
   
(* constraintとunknown predicate　からなるグラフ構造 *)
module G:
sig
  
  type cLavel = private int
                      
  val int_of_cLavel: cLavel -> int
    
  type pLavel = private int

  val int_of_pLavel: pLavel -> int


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

  type t = {cTable: cNode array;
            pTable: pNode array;
            pIdHash: (Id.t, pLavel) Hashtbl.t
           }

  val pLavel_of_id: t -> Id.t -> pLavel

  val id_of_pLavel: t -> pLavel -> Id.t

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
               ;neg: pLavel list
               }

  type t = {cTable: cNode array;
            pTable: pNode array
            ;pIdHash: (Id.t, pLavel) Hashtbl.t
           }

  let pLavel_of_id t id =
    try Hashtbl.find t.pIdHash id with
      Not_found -> invalid_arg "pLavel_of_id: invalid id"

  let id_of_pLavel t p =
    try t.pTable.(p).value with
      _ ->  invalid_arg "invalid lavel"

  let cons_of_cLavel t c =
    try t.cTable.(c).value with
      _ -> invalid_arg "invalid lavel"
         
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
      adj_map.pos.(k) <- (v::l)

    let add_neg adj_map k v =
      let l = adj_map.neg.(k) in
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
                   pos_ps
        in
        let () = S.iter
               (fun p ->
                 let p_lav = Hashtbl.find p_hash p in
                 (add_neg p_map p_lav c_lav);
                 (add_pos p_map p_lav c_lav))
               pos_ps
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
                   pos_ps
        in
        let () = S.iter
               (fun p ->
                 let p_lav = Hashtbl.find p_hash p in
                 (add_neg c_map c_lav p_lav);
                 (add_pos c_map c_lav p_lav))
               pos_ps
        in
        ()        
      
    (* p_map, c_mapを作成 *)
    let rec scan_sub_cs p_hash c_array p_map c_map  =function
      |(Constraint.SSub _) as c::other ->
        let pos_ps, neg_ps, othere_ps =
          Constraint.positive_negative_unknown_p c
        in
        let c_lav = add_c_array c_array c in
        let () = add_p_map p_hash p_map c_lav pos_ps neg_ps othere_ps in
        let () = add_c_map p_hash c_map c_lav pos_ps neg_ps othere_ps in
        scan_sub_cs p_hash c_array p_map c_map other
        
      |(Constraint.SWF _)::other ->
        scan_sub_cs p_hash c_array p_map c_map other
       
      |[] -> ()

    let rec scan_wf_cs p_hash p_env_array p_senv_array = function
      |Constraint.SWF (env, (senv, Formula.Unknown (_,_,_,p)))::other ->
        let p_lav = Hashtbl.find p_hash p in
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
      {cTable = c_table
      ;pTable = p_table
      ;pIdHash = p_hash
      }
      
      
      
                   
    let f up_ps cs =
      let p_hash = Hashtbl.create 1000 in
      let p_count = !plav_count in
      let c_count = List.length cs in
      let () = mk_p_hash p_hash cs in
      let c_array = Array.make c_count (List.hd cs) in
      let p_map = create_adj_map p_count in
      let c_map = create_adj_map p_count  in
      (* initialize c_array, p_map, c_map *)
      let () = scan_sub_cs p_hash c_array p_map c_map cs in
      let p_env_array = Array.make p_count Liq.env_empty in
      let p_senv_array = Array.make p_count Formula.Senv.empty in
      (* initialize p_env_array p_senv_array *)
      let () = scan_wf_cs p_hash p_env_array p_senv_array cs in
      mk_graph up_ps p_hash c_array p_map c_map p_env_array p_senv_array
      
    
    end

    

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



          
