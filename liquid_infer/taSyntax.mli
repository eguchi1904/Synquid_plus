(* type(:'a) annotation *)
type 'a t = PLet of (Id.t * 'a)  * 'a t * 'a t
          (* let x:schema= e1 in e2 *)
          |PE of 'a e | PI of 'a b | PF of 'a f | PHole
                                 
 and 'a e =                        (* E-term *)
   |PSymbol of (Id.t *  'a list)     (* x[t1,t2, ... ] *)
   |PAuxi of Id.t               (* auxiliary function *)
   |PAppFo of 'a e * 'a e
                                 
 and 'a b =                        (* branching-term *)
   |PIf of 'a e * 'a t * 'a t
   |PMatch of 'a e * (('a case) list)

 (* \x.t.(body) *)
 and 'a f =
   |PFun of (Id.t * 'a)  * 'a t


 and 'a case = {constructor : Id.t ; argNames : (Id.t * 'a) list ; body : 'a t}

val syn2string: ('a -> string) -> 'a t -> string
             
val access_annotation_t: ('a -> 'a) ->('a t) -> ('a t)
val access_annotation_e: ('a -> 'a) ->('a e) -> ('a e)
val access_annotation_b: ('a -> 'a) ->('a b) -> ('a b)
val access_annotation_f: ('a -> 'a) ->('a f) -> ('a f)
               
