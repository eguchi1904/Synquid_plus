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

    
module PredicateFixableLevel:
sig
  type t = private int 
  val all: t
  val partial: t        (* partial is_hinted *)
  val zero:  t           (* zero is_hinted *)
  val to_string: t -> string
end = struct
  type t =  int
  let all  = 0
  let partial  = 1
  let zero  = 2

  let to_string t =
    if t = all then "all"
    else if t = partial then "partial"
    else if t = zero then "zero"
    else assert false
end

module PreferedPolarity:
sig
  type t = private int
  val any:t                 
  val pos:t
  val neg:t
end = struct
  type t = int

  let any = 0
  let pos = 1
  let neg = 2

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
          
  let compare = compare
end

(* priorityを計算するために必要な情報 *)
module PredicateInfo = struct
  type t ={fixLevel: PredicateFixableLevel.t
          ;otherPCount: int option
          ;fixableNum: int option
          ;pol: Polarity.t
          ;lavel: G.pLavel }

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
    
    Priority.{fixLevel = p_info.PredicateInfo.fixLevel
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
    let prefer = prefered_pol.(G.int_of_pLavel p) in
    if prefer = PreferedPolarity.neg then
      ()
    else if prefer = PreferedPolarity.pos then
      begin
        table.(G.int_of_pLavel p) <- priority;
        InternalQueue.push internal_queue priority
      end
    else
      begin
        pos_table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
        let neg_priority = neg_table.(G.int_of_pLavel p) in
        let min_priority = min priority neg_priority in
        if min_priority < table.(G.int_of_pLavel p)  then
          (table.(G.int_of_pLavel p) <- min_priority;
           InternalQueue.push internal_queue min_priority)
        else
          ()
      end

    
  let push_neg {preferedPol = prefered_pol
               ;posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority =
    let prefer = prefered_pol.(G.int_of_pLavel p) in
    if prefer =  PreferedPolarity.pos then
      ()
    else if prefer = PreferedPolarity.neg then
      begin
        table.(G.int_of_pLavel p) <- priority;
        InternalQueue.push internal_queue priority
      end
    else
      begin
        neg_table.(G.int_of_pLavel p) <- priority; (* table kept up to date *)
        let pos_priority = pos_table.(G.int_of_pLavel p) in
        let min_priority = min priority  pos_priority in
        if min_priority < pos_table.(G.int_of_pLavel p) then
          (table.(G.int_of_pLavel p) <- min_priority;
           InternalQueue.push internal_queue min_priority)
        else
          ()
      end
       

  let update_pos = push_pos

  let update_neg = push_neg

      
end
