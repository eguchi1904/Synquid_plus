module Heap = Core.Heap         (* heapのためだけに、Core依存 *)
            
module G = ConsGraph.G
module PMap = ConsGraph.PMap
module PSet = ConsGraph.PSet
            
            

                  
module Polarity:
sig
  type t = private int
  val pos: t
  val neg: t
  val of_string: t -> string
end = struct
  type t = int
  let pos = 1
  let neg = 0                   (*  negativeのが優先順位高いかな *)
  let of_string pol =
    if pol = pos then "pos"
    else if pol = neg  then "neg"
    else
      assert false
end

module PreferedPolarity:
sig
  type t = private int
  val any:t                 
  val pos:t
  val neg:t
  val is_prefered: t -> Polarity.t -> bool
end = struct
  type t = int

  let any = 0
  let pos = 1
  let neg = 2

  let is_prefered (t:t) (pol:Polarity.t) =
    (t = any) ||(t = pos && pol = Polarity.pos)||(t = neg && pol = Polarity.neg)
      
    

end
          

    
module PredicateFixableLevel:
sig
  type t = private int 
  val all: t
  val partial: t        (* partial is_hinted *)
  val twist: t          (* prefered polarityと逆の制約でfixableなのがある状態 *)
  val zero:  t           (* zero is_hinted *)
  val add_twisted_info: t -> Polarity.t -> PreferedPolarity.t -> int option -> t
  val to_string: t -> string
end = struct
  type t =  int
  let all  = 0
  let partial  = 1
  let twist = 2
  let zero  = 3

  let add_twisted_info fix_level pol prefere_pol fixable_num_opt =
    if PreferedPolarity.is_prefered prefere_pol pol then
      fix_level                 (* no change *)
    else if(fix_level = partial)||(fix_level = all && fixable_num_opt <> Some 0) then
      twist
    else
      zero
      
      
      
  let to_string t =
    if t = all then "all"
    else if t = partial then "partial"
    else if t = zero then "zero"
    else if t = twist then "twist"
    else assert false
end
    


module PredicateInfo = struct
  type t ={fixLevel: PredicateFixableLevel.t
          ;otherPCount: int option
          ;fixableNum: int option
          ;pol: Polarity.t
          ;lavel: G.pLavel }

end            
    
    
module Priority = struct
  (* the most important factor is fixable level *)
  type t = {fixLevel: PredicateFixableLevel.t
           ;preferedPol: PreferedPolarity.t
           ;otherPCount: int
           ;fixableNum:int
           ;pol: Polarity.t
           ;lavel: G.pLavel }

  let to_string graph t =
    Printf.sprintf "{%s; otherPCouunt:%d; fixableNum:%d; %s; %s}"
                   (PredicateFixableLevel.to_string t.fixLevel)
                   t.otherPCount
                   t.fixableNum
                   (Polarity.of_string t.pol)
                   (G.id_of_pLavel graph t.lavel)

    
  (* priorityの値が小さい方が優先順位が低い
   言葉の意味が反転してしまっている*)
  let max = {fixLevel = PredicateFixableLevel.zero
            ;preferedPol = PreferedPolarity.neg
            ;otherPCount = max_int
            ;fixableNum = max_int
            ;pol = Polarity.pos
            ;lavel = G.def_pLavel }
          
  let compare rc1 rc2 =
    (*  *)
    if rc1.fixLevel <> rc2.fixLevel then
      compare rc1.fixLevel rc2.fixLevel
    else if rc1.preferedPol <> rc2.preferedPol then
      compare rc1.preferedPol rc2.preferedPol
    else if rc1.otherPCount <> rc2.otherPCount then
      compare rc1.otherPCount rc2.otherPCount
    else if rc1.fixableNum <> rc2.fixableNum then
      compare rc1.fixableNum rc2.fixableNum
    else if rc1.pol <> rc2.pol then
      compare rc1.pol rc2.pol
    else
      compare rc1.lavel rc2.lavel (* 反転 *)
    
end
            
module PriorityQueue:
sig

  type t

  val to_string: G.t -> t -> string

  val calc_priority: t -> PredicateInfo.t -> Priority.t

  val pop: t -> (G.pLavel * Polarity.t * Priority.t) option

  val push_pos: t -> G.pLavel -> Priority.t -> unit

  val push_neg: t -> G.pLavel -> Priority.t -> unit    

  val update_pos: t -> G.pLavel -> Priority.t -> unit

  val update_neg: t -> G.pLavel -> Priority.t -> unit

  val create: PSet.t -> PSet.t -> int -> t

    
end  = struct


  
                  
  module InternalQueue:
  sig

    type t = private Priority.t Heap.t

    val create: int -> t

    val pop: t ->  Priority.t option

    val push: t -> Priority.t -> unit


  end = struct

    type t = Priority.t Heap.t

    let create size =
      Heap.create ~min_size:size ~cmp:Priority.compare ()

    let pop heap =
      match Heap.pop heap with
      |None -> None
      |Some priority -> Some priority

      
    let push heap priority= Heap.add heap priority


  end

  type t = {preferedPol: PreferedPolarity.t array   (* neg fixのみのもの *)
           ;posTable: Priority.t array
           ;negTable: Priority.t array
           ;table: Priority.t array
           ;internalQueue: InternalQueue.t
           }

  let to_string graph t =
    G.fold_p
      (fun p acc_str ->
        let p = G.int_of_pLavel p in
        let pos_priority = t.posTable.(p) in
        let neg_priority = t.negTable.(p) in
        let min_priority = t.table.(p) in
        let str = Printf.sprintf " pos - %s\n neg - %s\n min - %s\n"
                                 (Priority.to_string graph pos_priority)
                                 (Priority.to_string graph neg_priority)
                                 (Priority.to_string graph min_priority)
        in
        acc_str ^ "\n\n" ^str)
      graph
    ""
    
        
  (* up_ps は preferedPolは,neg *)
  let create_preferedPol up_ps down_ps size =
    let arr = Array.make size PreferedPolarity.any in
    let () = PSet.iter
               (fun p ->
                 arr.(G.int_of_pLavel p) <- PreferedPolarity.neg
               )
               up_ps
    in
    let () = PSet.iter
               (fun p ->
                 arr.(G.int_of_pLavel p) <- PreferedPolarity.pos
               )
               down_ps
    in
    arr


  let create up_ps down_ps size =             (* ここでdummyとしてはpriorityがすぐに更新されるようなもの *)
    {preferedPol = create_preferedPol up_ps down_ps size
    ;posTable = Array.make size Priority.max
    ;negTable =  Array.make size Priority.max
    ;table = Array.make size Priority.max
    ;internalQueue = InternalQueue.create size
    }    
    
    
  let calc_priority t p_info =
    let p = p_info.PredicateInfo.lavel in
    let prefer = t.preferedPol.(G.int_of_pLavel p) in
    let pol = p_info.PredicateInfo.pol in
    let init_fix_level = p_info.PredicateInfo.fixLevel in
    (* ad-hoc *)
    let fix_level = PredicateFixableLevel.add_twisted_info
                      init_fix_level
                      pol
                      prefer
                      p_info.PredicateInfo.fixableNum                  
    in
    let pc_count =
      match p_info.PredicateInfo.otherPCount with
      |Some i-> i
      |None -> -1               (* dummy *)
    in
    let fixable_num =
      match p_info.PredicateInfo.fixableNum with
      |Some i-> i
      |None -> -1               (* dummy *)
    in    
    
    Priority.{fixLevel = fix_level
             ;preferedPol = prefer
             ;otherPCount = pc_count
             ;fixableNum =  fixable_num
             ;pol = p_info.PredicateInfo.pol
             ;lavel = p
    }
    

  let rec pop ({table = table; internalQueue = internal_queue} as queue) =
    match InternalQueue.pop internal_queue with
    |None -> None
    |Some priority ->
      let p = priority.Priority.lavel in
      let priority' =  table.(G.int_of_pLavel p) in
      if priority = priority' then
        Some (p, priority.pol, priority)      (* table はpopされた時のものに保たれる *)
      else                        (* updated old element *)
        pop queue


  let push_pos {preferedPol = prefered_pol
               ;posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority =
    pos_table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    let neg_priority = neg_table.(G.int_of_pLavel p) in
    let min_priority = min priority neg_priority in
    if min_priority < table.(G.int_of_pLavel p)  then
      (table.(G.int_of_pLavel p) <- min_priority;
       InternalQueue.push internal_queue min_priority)
    else
      ()
    
    
  let push_neg {preferedPol = prefered_pol
               ;posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority =
    neg_table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
    let pos_priority = pos_table.(G.int_of_pLavel p) in
    let min_priority = min priority  pos_priority in
    if min_priority < pos_table.(G.int_of_pLavel p) then
      (table.(G.int_of_pLavel p) <- min_priority;
       InternalQueue.push internal_queue min_priority)
    else
      ()
       

  let update_pos = push_pos

  let update_neg = push_neg

      
end
