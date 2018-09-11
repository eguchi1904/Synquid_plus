open Extensions
(* type(:'a) annotation *)
type 'a t = PLet of (Id.t * 'a)  * 'a t * 'a t
          (* let x:schema= e1 in e2 *)
          |PE of 'a e | PI of 'a b | PF of 'a f | PHole
                                 
 and 'a e =                        (* E-term *)
   |PSymbol of (Id.t *  'a list)     (* x[t1,t2, ... ] *)
   |PAuxi of Id.t               (* auxiliary function *)
   |PAppFo of 'a e * 'a e
   |PAppHo of 'a e * 'a f            
                                 
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
  |PAppHo (e1, f2) -> PAppHo (access_annotation_e f e1, access_annotation_f f f2)

and access_annotation_b f b = match b with
  |PIf (e, t1, t2) -> PIf (access_annotation_e f e,
                           access_annotation_t f t1,
                           access_annotation_t f t2)
  |PMatch (e, case_list) -> PMatch( access_annotation_e f e,
                                    List.map (access_annotation_case f) case_list)

and access_annotation_f f (PFun ((x, sch), t1)) = PFun ((x, f sch), access_annotation_t f t1)

and access_annotation_case f {constructor =  c; argNames = x_sch_list; body = t} =
  {constructor = c;
   argNames = List.map (fun (x, sch) -> (x, f sch)) x_sch_list;
   body = access_annotation_t f t}

  

let rec substitute (x:Id.t) (dest:'a e) (t:'a t)  = match t with
  |PLet ((y, sch), t1, t2) when y = x ->  t
  |PLet ((y, sch), t1, t2) ->
    PLet ((y, sch), (substitute x dest t1), (substitute x dest t2))
  |PE e -> PE (substitute_e x dest e)
  |PI b -> PI (substitute_b x dest b)
  |PF f -> PF (substitute_f x dest f)
  |PHole -> PHole

and substitute_e (x:Id.t) (dest:'a e) (e:'a e) =  match e with
  |PSymbol (i, sch) when i = x ->  dest
  |PSymbol (i, sch) -> PSymbol (i, sch)
  |PAuxi i -> PAuxi i
  |PAppFo (e1, e2) -> PAppFo (substitute_e x dest e1, substitute_e x dest e2)
  |PAppHo (e1, f2) -> PAppHo (substitute_e x dest e1, substitute_f x dest f2)

and substitute_b x dest b = match b with
  |PIf (e1, t2, t3) -> PIf (substitute_e x dest e1, substitute x dest t2, substitute x dest t3)
  |PMatch (e, case_list) ->
    PMatch (substitute_e x dest e, List.map (substitute_case x dest) case_list)

and substitute_case x dest {constructor =  c; argNames = x_sch_list; body = t } =
  if List.mem_assoc x x_sch_list then
    {constructor =  c; argNames = x_sch_list; body = t }
  else
    {constructor =  c; argNames = x_sch_list; body = substitute x dest t }

and substitute_f x dest  (PFun ((y, sch), t1)) =
  if x = y then
    (PFun ((y, sch), t1))
  else
    (PFun ((y, sch), substitute x dest t1))
                     

  

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
  |PAppHo (e1, fterm) -> Printf.sprintf "%s (%s)" (syn2string_e f e1) (syn2string_f f fterm)

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





  
  
let rec fv t = match t with
  |PLet ((x, anno), t1, t2) ->
    S.remove x (S.union (fv t1) (fv t2))
  |PE e -> fv_e  e
  |PI b -> fv_b  b
  |PF fundec -> fv_f  fundec
  |PHole -> S.empty

and fv_e  = function
  |PSymbol (i, xs) -> S.singleton i
  |PAuxi i -> S.singleton i
  |PAppFo (e1,e2) -> (S.union (fv_e e1) (fv_e e2))
  |PAppHo (e1, fterm) -> (S.union (fv_e e1) (fv_f fterm))

and fv_b  = function
  |PIf (e,t1,t2) ->
    (S.union (fv_e e) (S.union (fv t1) (fv t2)))
  |PMatch (e, cases) ->
    S.union (fv_e e)
            (List.fold_left
               (fun acc case -> S.union acc (fv_case case))
               S.empty
               cases
            )
   
and fv_f  = function
  |PFun ((x, anno), t) ->
    S.remove x (fv t)

and fv_case  {constructor = cons; argNames = xs; body = t} =
  S.diff (fv t) (S.of_list (List.map fst xs))


  


  

    
