(* type(:'a) annotation *)
type 'a t = PLet of (Id.t * 'a)  * 'a t * 'a t
          (* let x:schema= e1 in e2 *)
          |PE of 'a e | PI of 'a b | PF of 'a f | PHole
                                 
 and 'a e =                        (* E-term *)
   |PSymbol of (Id.t *  'a list)     (* x[t1,t2, ... ] *)
   |PAuxi of (Id.t * 'a)          (* auxiliary function *)
   |PInnerFun of 'a f           
   |PAppFo of 'a e * 'a e
   |PAppHo of 'a e * 'a f
                                 
 and 'a b =                        (* branching-term *)
   |PIf of 'a e * 'a t * 'a t
   |PMatch of 'a e * (('a case) list)

 (* \x.t.(body) *)
 and 'a f =
   |PFun of (Id.t * 'a)  * 'a t
   |PFix of (Id.t * 'a * 'a list) * 'a f


 and 'a case = {constructor : Id.t ; argNames : (Id.t * 'a) list ; body : 'a t}


val mk_case: Id.t -> Id.t list -> 'a option t -> 'a option case (* for parser *)

val remove_annotations: 'a t -> Syntax.t
val remove_annotations_e: 'a e -> Syntax.e
val remove_annotations_b: 'a b -> Syntax.b
val remove_annotations_f: 'a f -> Syntax.f

val add_empty_annotation: Syntax.t -> 'a option t
val add_empty_annotation_e: Syntax.e -> 'a option e
             
val substitute:   Id.t -> 'a e -> 'a t -> 'a t
val substitute_f: Id.t -> 'a e -> 'a f -> 'a f
val syn2string: ('a -> string) -> 'a t -> string
             
val access_annotation_t: ('a -> 'b) ->('a t) -> ('b t)
val access_annotation_e: ('a -> 'b) ->('a e) -> ('b e)
val access_annotation_b: ('a -> 'b) ->('a b) -> ('b b)
val access_annotation_f: ('a -> 'b) ->('a f) -> ('b f)

val replace:  Id.t M.t ->('a t) -> ('a t)
val replace_e: Id.t M.t ->('a e) -> ('a e)
val replace_b: Id.t M.t ->('a b) -> ('a b)
val replace_f: Id.t M.t  ->('a f) -> ('a f)  

val fold_let_anno: (Id.t -> 'a -> 'b -> 'b) ->'a t -> 'b -> 'b
               
val fv: 'a t -> S.t

val auxi_exist_t: 'a t -> bool

val get_auxi_anno: 'a t -> 'a M.t


