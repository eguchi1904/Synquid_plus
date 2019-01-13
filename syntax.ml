type t = PLet of Id.t * t * t |PE of e | PI of b | PF of f | PHole
                                 
 and e =                        (* E-term *)
   |PSymbol of Id.t             (* Symbol - variable , constract *)
   |PAuxi of Id.t               (* auxiliary function *)
   |PInnerFun of f
   |PAppFo of e * e
   |PAppHo of e * f             (* redundant *)
                                 
 and b =                        (* branching-term *)
   |PIf of e * t * t
   |PMatch of e * (case list)

 and f =
   |PFun of Id.t * t
   |PFix of Id.t * f

 and case = {constructor : Id.t ; argNames : Id.t list ; body : t}

  
let rec fv t = match t with
  |PLet (x, t1, t2) ->
    S.remove x (S.union (fv t1) (fv t2))
  |PE e -> fv_e  e
  |PI b -> fv_b  b
  |PF fundec -> fv_f  fundec
  |PHole -> S.empty

and fv_e  = function
  |PSymbol i -> S.singleton i
  |PAuxi i -> S.singleton i
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
  |PFun (x, t) ->
    S.remove x (fv t)
  |PFix (f_name, body) ->
    S.remove f_name (fv_f body)

and fv_case  {constructor = cons; argNames = xs; body = t} =
  S.diff (fv t) (S.of_list xs)


  



let rec auxi_exist (e:e) =
  match e with
  |PSymbol _ -> false
  |PAuxi _ -> true
  |PInnerFun f -> auxi_exist_f f
  |PAppFo (e1, e2) ->(auxi_exist e1)||(auxi_exist e2)
  |PAppHo (e1, f2) ->(auxi_exist e1)||(auxi_exist_f f2)

and auxi_exist_f (f:f) = match f with
  |PFun (x, t) -> (auxi_exist_t t)
  |PFix (x, f) -> (auxi_exist_f f)

and auxi_exist_t (t:t) = match t with
  |PLet (x, t1, t2) -> (auxi_exist_t t1)||(auxi_exist_t t2)
  |PE e -> (auxi_exist e)
  |PI b -> (auxi_exist_b b)
  |PF f -> (auxi_exist_f f)
  |PHole -> false

and auxi_exist_b (b:b) = match b with
  |PIf (e1, t1, t2) -> (auxi_exist e1)||(auxi_exist_t t1)||(auxi_exist_t t2)
  |PMatch (e, case_list) -> (auxi_exist e)||(List.exists auxi_exist_case case_list)

and auxi_exist_case case = auxi_exist_t case.body


                          
                     
                     

let rec auxi_name (e:e) =
  match e with
  |PSymbol _ -> raise (Invalid_argument "auxi_function not found")
  |PInnerFun _ ->raise (Invalid_argument "auxi_function not found")
  |PAuxi i ->  i
  |PAppFo (e1,e2) -> auxi_name e1
  |PAppHo (e1, f) -> auxi_name e1

let mk_case a b c = {constructor=a; argNames=b; body=c }

let rec syn2string = function
  |PLet (x, t1, t2) ->
    Printf.sprintf "let %s = %s \n %s"
                   x
                   (syn2string t1)
                   (syn2string t2)   
  |PE e -> syn2string_e e
  |PI b -> syn2string_b b
  |PF f -> syn2string_f f
  |PHole -> "??"

and syn2string_e = function
  |PSymbol i -> i
  |PAuxi i -> i
  |PInnerFun f -> (syn2string_f f)
  |PAppFo (e1,e2) -> Printf.sprintf "%s (%s)" (syn2string_e e1) (syn2string_e e2)
  |PAppHo (e1, f2) -> Printf.sprintf "%s (%s)" (syn2string_e e1) (syn2string_f f2)

and syn2string_b = function
  |PIf (e,t1,t2) ->
    Printf.sprintf "if %s then \n %s \n else %s \n"
                   (syn2string_e e)
                   (syn2string t1)
                   (syn2string t2)
  |PMatch (e, cases) ->
    Printf.sprintf "\nmatch %s with \n%s "
                  (syn2string_e e)
                  (String.concat "\n" (List.map syn2string_case cases))

and syn2string_f = function
  |PFun (x,t) ->
    Printf.sprintf "\\%s.%s" x (syn2string t)
  |PFix (x,f) -> syn2string_f f

and syn2string_case {constructor = cons; argNames = xs; body = t} =
  Printf.sprintf " %s %s -> %s" cons (String.concat " " xs) (syn2string t)

(* [e_1; e_2; e3] -> ((e_1 e_2) e_3)  *)
let mk_fun_app_term: e -> Id.t list -> e =
  (fun f vars ->
    List.fold_left (fun e_acc id -> PAppFo (e_acc, PSymbol id)) f vars
  )

let elist_2_e: e -> e list -> e =
  (fun f args ->
    List.fold_left (fun e_acc e -> PAppFo (e_acc, e)) f args)
        
let let_rec: Id.t -> Id.t list -> t -> t=
  (fun f args e ->
    let fun_dec = List.fold_right (fun arg t_acc -> (PF (PFun (arg, t_acc)))) args e in
    match fun_dec with
    |PF body -> PF (PFix (f, body))
    |_ -> assert false
  )


(* inline recurisive fuctnion *)
let rec inline_rec_fun env e =
  match e with
  |PLet (x, t1, t2) when not (S.mem x (fv t1)) -> (* not recusion *)
    let t1' = inline_rec_fun env t1 in
    PLet (x, t1', inline_rec_fun (M.remove x env) t2)
  |PLet (f_rec, (PF f_body), t2) -> (* recurisive function *)
    let f_body' = inline_rec_fun_f env f_body in
    let fix_val = PInnerFun (PFix (f_rec, f_body')) in
    inline_rec_fun (M.add f_rec fix_val env) t2
  |PLet _ -> assert false
  |PE e -> PE (inline_rec_fun_e env e)
  |PI b -> PI (inline_rec_fun_b env b)
  |PF f -> PF (inline_rec_fun_f env f)
  |PHole -> PHole

and inline_rec_fun_e env = function
  |PSymbol i when (M.mem i env) -> M.find i env
  |PSymbol i|PAuxi i as e -> e
  |PInnerFun f -> PInnerFun (inline_rec_fun_f env f)
  |PAppFo (e1,e2) -> PAppFo (inline_rec_fun_e env e1, inline_rec_fun_e env e2)
  |PAppHo (e1, f2) -> PAppHo (inline_rec_fun_e env e1, inline_rec_fun_f env f2)

and inline_rec_fun_b env = function
  |PIf (e,t1,t2) ->
    PIf (inline_rec_fun_e env e, inline_rec_fun env t1, inline_rec_fun env t2)
  |PMatch (e, cases) ->    
    PMatch (inline_rec_fun_e env e, List.map (inline_rec_fun_case env) cases)

and inline_rec_fun_case env  {constructor = cons; argNames = xs; body = t} =
  {constructor = cons; argNames = xs; body = inline_rec_fun env t}

and inline_rec_fun_f env = function
  |PFun (x, t) ->
    let t' = inline_rec_fun (M.remove x env) t in
    PFun (x, t')
  |PFix (f_name, body) ->
    let body' = inline_rec_fun_f (M.remove f_name env) body in
    PFix (f_name, body')

    
let rec alpha env = function
  |PLet (y, t1, t2) ->
    let y' = Id.genid y in
    let env' = M.add y y' env in
    PLet (y', (alpha env' t1), (alpha env' t2))
  |PE e -> PE (alpha_e env e)
  |PI b -> PI (alpha_b env b)
  |PF f -> PF (alpha_f env f)
  |PHole -> PHole

and alpha_e env  = function
  |PSymbol i when M.mem i env -> PSymbol (M.find i env)
  |PSymbol i -> PSymbol i
  |PInnerFun f_in -> PInnerFun (alpha_f env f_in)
  |PAuxi i -> PAuxi i
  |PAppFo (e1, e2) -> PAppFo (alpha_e env e1, alpha_e env e2)
  |PAppHo (e1, f2) -> PAppHo (alpha_e env e1, alpha_f env f2)

and alpha_b env b = match b with
  |PIf (e1, t2, t3) -> PIf (alpha_e env e1, alpha env  t2, alpha env t3)
  |PMatch (e, case_list) ->
    PMatch (alpha_e env e, List.map (alpha_case env) case_list)

and alpha_case env {constructor =  c; argNames = xs; body = t } =
  let xs' = (List.map Id.genid xs) in
  let env' = M.add_list2 xs xs' env in
  {constructor =  c; argNames = xs'; body = alpha env' t }

and alpha_f env  =function
  |PFun (y, t1) ->
    let y' = Id.genid y in
    let env' = M.add y y' env in
    (PFun (y', alpha env' t1))
  |PFix (f_name, body) ->
    PFix (f_name, alpha_f env body)
                     
