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
               ;pos:pLavel
               ;neg:pLavel list}

  type pNode = {lavel:int
               ;value:Id.t
               ;isUpp: bool
               ;env:Liq.env
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

  val pos_p: t -> cLavel -> pLavel

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
               ;pos:pLavel
               ;neg:pLavel list}

  type pNode = {lavel:int
               ;value:Id.t
               ;isUpp: bool               
               ;env: Liq.env
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
         
  let pos_p graph c_lav =
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



          
