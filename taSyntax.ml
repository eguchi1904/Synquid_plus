open Extensions
(* type(:'a) annotation *)
type 'a t = PLet of (Id.t * 'a)  * 'a t * 'a t
          (* let x:schema= e1 in e2 *)
          |PE of 'a e | PI of 'a b | PF of 'a f | PHole
                                 
 and 'a e =                        (* E-term *)
   |PSymbol of (Id.t *  'a list)     (* x[t1,t2, ... ] *)
   |PAuxi of (Id.t * 'a)              (* auxiliary function *)
   |PInnerFun of 'a f
   |PAppFo of 'a e * 'a e
   |PAppHo of 'a e * 'a f       (* redundant *)
                                 
 and 'a b =                        (* branching-term *)
   |PIf of 'a e * 'a t * 'a t
   |PMatch of 'a e * (('a case) list)

 (* \x.t.(body) *)
 and 'a f =
   |PFun of (Id.t * 'a)  * 'a t
   |PFix of (Id.t * 'a * 'a list) * 'a f


 and 'a case = {constructor : Id.t ; argNames : (Id.t * 'a) list ; body : 'a t}

let rec remove_annotations = function
  |PLet ((x, _), t1, t2) -> Syntax.PLet (x, remove_annotations t1, remove_annotations t2)
  |PE e -> Syntax.PE (remove_annotations_e e)
  |PI b -> Syntax.PI (remove_annotations_b b)
  |PF f -> Syntax.PF (remove_annotations_f f)
  |PHole -> Syntax.PHole

and remove_annotations_e = function
  |PSymbol (x, _) -> Syntax.PSymbol x
  |PAuxi (i, _) -> Syntax.PAuxi i
  |PInnerFun f_in -> Syntax.PInnerFun (remove_annotations_f f_in)
  |PAppFo (e1, e2)-> Syntax.PAppFo (remove_annotations_e e1, remove_annotations_e e2)
  |PAppHo (e1, f2) -> Syntax.PAppHo (remove_annotations_e e1, remove_annotations_f f2)


and remove_annotations_b = function
  |PIf (e1, t2, t3) -> Syntax.PIf (remove_annotations_e e1, remove_annotations t2, remove_annotations t3)
  |PMatch (e, case_list) ->
    Syntax.PMatch (remove_annotations_e e, List.map remove_annotations_case case_list)

and remove_annotations_case {constructor =  c; argNames = x_sch_list; body = t } =
  Syntax.{constructor =  c; argNames = List.map fst x_sch_list; body = remove_annotations  t }

and remove_annotations_f = function
  |PFun ((y, _), t1) ->
    Syntax.PFun (y, remove_annotations t1)

  |PFix ((f_name, _, _), body) ->
    Syntax.PFix (f_name, remove_annotations_f body)

let rec add_empty_annotation = function
  |Syntax.PLet (x, t1, t2) ->
    PLet ((x, None),
          add_empty_annotation t1,
          add_empty_annotation t2)
  |Syntax.PE e -> PE (add_empty_annotation_e e)
  |Syntax.PI b -> PI (add_empty_annotation_b b)
  |Syntax.PF f -> PF (add_empty_annotation_f f)
  |Syntax.PHole -> PHole

and add_empty_annotation_e = function
  |Syntax.PSymbol i -> PSymbol (i, [])
  |Syntax.PInnerFun f -> PInnerFun (add_empty_annotation_f f)
  |Syntax.PAppFo (e1, e2) ->
    PAppFo (add_empty_annotation_e e1,
            add_empty_annotation_e e2)
  |Syntax.PAppHo (e1, f2) ->
    PAppHo (add_empty_annotation_e e1,
            add_empty_annotation_f f2)
  |Syntax.PAuxi i -> PAuxi (i, None)

and add_empty_annotation_b = function
  |Syntax.PIf (e, t1, t2) ->
    PIf (add_empty_annotation_e e,
         add_empty_annotation t1,
         add_empty_annotation t2)
  |Syntax.PMatch (e, cases) ->
    PMatch (add_empty_annotation_e e,
            List.map add_empty_annotation_case cases)

and add_empty_annotation_case Syntax.{constructor = cons;
                                      argNames = xs;
                                      body = t} =
  let xs' = List.map (fun x -> (x, None)) xs in
  let t' = add_empty_annotation t in
  {constructor = cons;
   argNames = xs';
   body = t'
  }

and add_empty_annotation_f = function
  |Syntax.PFun (x, t) ->
    PFun ((x,None),
          add_empty_annotation t)
  |Syntax.PFix _ -> assert false
    
    
                     
                 
         
let rec access_annotation_t (f:'a -> 'b) (t:'a t) = match t with
  |PLet ((x, sch), t1, t2) -> PLet ((x, (f sch)),
                                    (access_annotation_t f t1),
                                    (access_annotation_t f t2))
  |PE e -> PE (access_annotation_e f e)
  |PI b -> PI (access_annotation_b f b)
  |PF func -> PF (access_annotation_f f func)
  |PHole -> PHole

and access_annotation_e f e = match e with
  |PSymbol (x, ty_list) -> PSymbol (x, List.map f ty_list)
  |PAuxi (g,anno) -> PAuxi (g, f anno)
  |PInnerFun f_in -> PInnerFun (access_annotation_f f f_in)
  |PAppFo (e1, e2)-> PAppFo (access_annotation_e f  e1, access_annotation_e f e2)
  |PAppHo (e1, f2) -> PAppHo (access_annotation_e f e1, access_annotation_f f f2)

and access_annotation_b f b = match b with
  |PIf (e, t1, t2) -> PIf (access_annotation_e f e,
                           access_annotation_t f t1,
                           access_annotation_t f t2)
  |PMatch (e, case_list) -> PMatch( access_annotation_e f e,
                                    List.map (access_annotation_case f) case_list)

and access_annotation_f f = function
  |(PFun ((x, sch), t1)) -> PFun ((x, f sch), access_annotation_t f t1)
  |(PFix ((fname, sch, inst_tys), f_body)) ->  (PFix ((fname, f sch,
                                                       List.map f inst_tys), access_annotation_f f f_body))

and access_annotation_case f {constructor =  c; argNames = x_sch_list; body = t} =
  {constructor = c;
   argNames = List.map (fun (x, sch) -> (x, f sch)) x_sch_list;
   body = access_annotation_t f t}

  
(* プログラへの代入 *)
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
  |PInnerFun f_in -> PInnerFun (substitute_f x dest f_in)
  |PAuxi (g, sch) -> PAuxi (g,sch)
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

and substitute_f x dest f =
  match f with
  |PFun ((y, sch), t1) ->
    if x = y then
      (PFun ((y, sch), t1))
    else
      (PFun ((y, sch), substitute x dest t1))
  |PFix ((f_name, sch, inst_tys), body) ->
    if x = f_name then
      f
    else
      PFix ((f_name, sch, inst_tys), substitute_f x dest body)
                     

  

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
  |PInnerFun f_in -> Printf.sprintf "(%s)" (syn2string_f f f_in)
  |PAuxi (i, anno) -> Printf.sprintf "%s:%s"  i (f anno)
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
  |PFix ((fname, anno, inst_tys), f_body) ->
    let inst_tys_str = String.concat "; " (List.map f inst_tys) in
    Printf.sprintf "fix %s:%s; inst_tys:[%s]\n%s"
                   fname
                   (f anno)
                   inst_tys_str
                   (syn2string_f f f_body)


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
  |PAuxi (i,_) -> S.singleton i
  |PInnerFun f_in -> fv_f f_in
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
  |PFix ((f_name, sch, inst_tys), body) ->
    S.remove f_name (fv_f body)

and fv_case  {constructor = cons; argNames = xs; body = t} =
  S.diff (fv t) (S.of_list (List.map fst xs))



let rec replace env = function
  |PLet ((y,sch), t1, t2) ->
    if M.mem y env then
      let env' = M.remove y env in
      PLet ((y, sch), replace env t1, replace env' t2)
    else
      PLet ((y, sch), (replace env t1), (replace env t2))
  |PE e -> PE (replace_e env e)
  |PI b -> PI (replace_b env b)
  |PF f -> PF (replace_f env f)
  |PHole -> PHole

and replace_e env  = function
  |PSymbol (i, sch) when M.mem i env -> PSymbol ((M.find i env), sch)
  |PSymbol i_sch -> PSymbol i_sch
  |PInnerFun f_in -> PInnerFun (replace_f env f_in)
  |PAuxi i -> PAuxi i
  |PAppFo (e1, e2) -> PAppFo (replace_e env e1, replace_e env e2)
  |PAppHo (e1, f2) -> PAppHo (replace_e env e1, replace_f env f2)

and replace_b env b = match b with
  |PIf (e1, t2, t3) -> PIf (replace_e env e1, replace env  t2, replace env t3)
  |PMatch (e, case_list) ->
    PMatch (replace_e env e, List.map (replace_case env) case_list)

and replace_case env {constructor =  c; argNames = xs; body = t } =
  let env' = M.filter (fun x _ -> not (List.mem_assoc x xs)) env in
  {constructor =  c; argNames = xs; body = replace env' t }

and replace_f env  =function
  |PFun ((y, sch), t1) ->
    if M.mem y env then
      let env' = M.remove y env in
      (PFun ((y, sch), replace env' t1))
    else
      (PFun ((y, sch), replace env t1))
  |PFix ((f_name, sch, alist), body) ->
    if M.mem f_name env then
      let env' = M.remove f_name env in
      PFix ((f_name, sch, alist), replace_f env' body)
    else
      PFix ((f_name, sch, alist), replace_f env body)
                     
  
  

    

  
  
let rec get_auxi_anno t = match t with
  |PLet ((x, anno), t1, t2) ->
    M.union
      (fun g anno1 anno2 -> (assert (anno1 = anno2));Some anno1)
      (get_auxi_anno t1)
      (get_auxi_anno t2)
  |PE e -> get_auxi_anno_e  e
  |PI b -> get_auxi_anno_b  b
  |PF fundec -> get_auxi_anno_f fundec
  |PHole -> M.empty

and get_auxi_anno_e  = function
  |PSymbol (i, xs) -> M.empty
  |PAuxi (i, anno) -> M.singleton i anno
  |PInnerFun f_in -> get_auxi_anno_f f_in
  |PAppFo (e1,e2) ->
    M.union
      (fun g anno1 anno2 -> (assert (anno1 = anno2));Some anno1)
      (get_auxi_anno_e e1)
      (get_auxi_anno_e e2)
  |PAppHo (e1, fterm) ->
    M.union
      (fun g anno1 anno2 -> (assert (anno1 = anno2));Some anno1)
      (get_auxi_anno_e e1)
      (get_auxi_anno_f fterm)

and get_auxi_anno_b  = function
  |PIf (e,t1,t2) ->
    M.union
      (fun g anno1 anno2 -> (assert (anno1 = anno2));Some anno1)
      (get_auxi_anno t1)
      (get_auxi_anno t2)
    |>
      M.union
        (fun g anno1 anno2 -> (assert (anno1 = anno2));Some anno1)
        (get_auxi_anno_e e)   

  |PMatch (e, cases) ->
    List.fold_left
      (fun acc case ->
        M.union (fun g anno1 anno2 -> (assert (anno1 = anno2));Some anno1)
                (get_auxi_anno_case case)
                acc
      )
      (get_auxi_anno_e e)
      cases
   
   
and get_auxi_anno_f  = function
  |PFun ((x, anno), t) ->
    get_auxi_anno t
  |PFix ((f_name, sch, inst_tys), body) ->
    get_auxi_anno_f body

and get_auxi_anno_case  {constructor = cons; argNames = xs; body = t} =
  get_auxi_anno t

