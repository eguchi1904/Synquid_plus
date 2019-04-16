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
end = struct
  type t =  int
  let all  = 0
  let partial  = 1
  let zero  = 2
end

    
module Priority = struct
  (* the most important factor is fixable level *)
  type t = {fixLevel: PredicateFixableLevel.t
           ;otherPCount: int
           ;fixableNum:int
           ;pol: Polarity.t
           ;lavel: G.pLavel }

  (* priorityの値が小さい方が優先順位が低い
   言葉の意味が反転してしまっている*)
  let max = {fixLevel = PredicateFixableLevel.zero
             ;otherPCount = max_int
             ;fixableNum = max_int
             ;pol = Polarity.pos
             ;lavel = G.def_pLavel }
          
  let compare = compare
end

                
module PriorityQueue:
sig

  type t

  val pop: t -> (G.pLavel * Polarity.t * Priority.t) option

  val push_pos: t -> G.pLavel -> Priority.t -> unit

  val push_neg: t -> G.pLavel -> Priority.t -> unit    

  val update_pos: t -> G.pLavel -> Priority.t -> unit

  val update_neg: t -> G.pLavel -> Priority.t -> unit

  val create: PSet.t -> int -> t

    
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

      
  type t = {isUpp: bool array   (* neg fixのみのもの *)
           ;posTable: Priority.t array
           ;negTable: Priority.t array
           ;table: Priority.t array
           ;internalQueue: InternalQueue.t
           }


  let create_isUpp up_ps size =
    let arr = Array.make size false in
    let () = PSet.iter
               (fun p ->
                 arr.(G.int_of_pLavel p) <- true
               )
               up_ps
    in
    arr
         
  let create up_ps size =             (* ここでdummyとしてはpriorityがすぐに更新されるようなもの *)
    {isUpp = create_isUpp up_ps size
    ;posTable = Array.make size Priority.max
    ;negTable =  Array.make size Priority.max
    ;table = Array.make size Priority.max
    ;internalQueue = InternalQueue.create size
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


  let push_pos {isUpp = is_upp
               ;posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority =
    
    if is_upp.(G.int_of_pLavel p) then
      ()
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

    
  let push_neg {isUpp = is_upp
               ;posTable = pos_table
               ;negTable = neg_table
               ;table = table
               ;internalQueue = internal_queue} p priority =
    if is_upp.(G.int_of_pLavel p) then
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
