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

             
let rec access_annotation_t (f:'a -> 'a) (t:'a t) = match t with
  |PLet ((x, sch), t1, t2) -> PLet ((x, (f sch)),
                                    (access_annotation_t f t1),
                                    (access_annotation_t f t2))
  |PE e -> PE (access_annotation_e f e)
  |PI b -> PI (access_annotation_b f b)
  |PF func -> PF (access_annotation_f f func)
  |PHole -> PHole

and access_annotation_e f e = match e with
  |PSymbol (x, ty_list) -> PSymbol (x, List.map f ty_list)
  |PAuxi i -> PAuxi i
  |PAppFo (e1, e2)-> PAppFo (access_annotation_e f  e1, access_annotation_e f e2)

and access_annotation_b f b = match b with
  |PIf (e, t1, t2) -> PIf (access_annotation_e f e,
                           access_annotation_t f t1,
                           access_annotation_t f t2)
  |PMatch (e, case_list) -> PMatch( access_annotation_e f e,
                                    List.map (access_annotation_case f) case_list)

and access_annotation_f f (PFun ((x, sch), t1)) = PFun ((x, f sch), access_annotation_t f t1)

and access_annotation_case f {constructor =  c; argNames = x_sch_list; body = t} =
  {constructor = c; argNames = List.map (fun (x, sch) -> (x, f sch)) x_sch_list; body = t}


  

let rec syn2string f t = match t with
  |PLet ((x, anno), t1, t2) ->
    Printf.sprintf "let %s:%s = %s \n %s"
                   x
                   (f anno)
                   (syn2string f t1)
                   (syn2string f t2)   
  |PE e -> syn2string_e f e
  |PI b -> syn2string_b f b
  |PF fundec -> syn2string_f f fundec
  |PHole -> "??"

and syn2string_e f = function
  |PSymbol (i, []) -> i
  |PSymbol (i, xs) -> Printf.sprintf "%s[%s]"
                                     i
                                     (String.concat "," (List.map f xs))
  |PAuxi i -> i
  |PAppFo (e1,e2) -> Printf.sprintf "%s (%s)" (syn2string_e f e1) (syn2string_e f e2)

and syn2string_b f = function
  |PIf (e,t1,t2) ->
    Printf.sprintf "if %s then \n %s \n else %s \n"
                   (syn2string_e f e)
                   (syn2string f t1)
                   (syn2string f t2)
  |PMatch (e, cases) ->
    Printf.sprintf "\nmatch %s with \n%s "
                  (syn2string_e f e)
                  (String.concat "\n" (List.map (syn2string_case f) cases))

and syn2string_f f = function
  |PFun ((x, anno), t) ->
    Printf.sprintf "\\%s:%s.%s" x  (f anno) (syn2string f t)


and syn2string_case f {constructor = cons; argNames = xs; body = t} =
  let xs' = List.map (fun (x, anno) -> Printf.sprintf "%s:%s" x (f anno)) xs in
  Printf.sprintf " %s %s -> %s" cons (String.concat " " xs') (syn2string f t)

                         
