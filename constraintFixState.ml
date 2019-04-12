module G = ConsGraph.G
         
type cInfo = {isFix: bool ref
             ;unknown_p_count:  int ref
             ;unknown_up_p_count: int ref
             }
           


type t = {isFix: bool array
         ;unknown_p_count: int array           
         ;unknown_up_p_count: int array
         }

let is_fixed t c = t.isFix.(G.int_of_cLavel c)

let isnt_fixed t c = not (is_fixed t c)

let fix t c  = 
  (t.isFix.(G.int_of_cLavel c) <- true)
  




