open Formula
open UseZ3

exception PredicateNotExist of string

let add_pcandi pcandi p_i e =
  try
    let candi = M.find p_i pcandi in
    if e = Bool true then
      pcandi
    else
      M.add p_i (e::candi) pcandi
  with
    Not_found ->
    if e = Bool true then
      M.add p_i [] pcandi
    else
      M.add p_i [e] pcandi

let subst_inv (sita:subst) :subst =
  M.fold
    (fun x p inv_sita ->
      match p with
      |Var (s,y) -> M.add y (Var (s,x)) inv_sita
      |_ -> inv_sita)
    sita
  M.empty
    
let rec guess_candidate' cs (pcandi:(t list) M.t) =
  match cs with
  |(env, Unknown _, Unknown _) :: cs' -> (* とりあえず *)
  (* raise (Invalid_argument "predicateunknown vs predicateunknown") *)
    guess_candidate' cs' pcandi
  |(env, Unknown (_, sita, i), e) :: cs' ->
    let sita_inv = subst_inv sita in
    let e' = substitution sita_inv e in
    guess_candidate' cs' (add_pcandi pcandi i e')
  |(env, e, Unknown (_,sita, i)) :: cs'->
    let sita_inv = subst_inv sita in
    let e' = substitution sita_inv e in    
    guess_candidate' cs' (add_pcandi pcandi i e')
  |_ :: cs' -> guess_candidate' cs' pcandi
  |[] ->
    pcandi

   
   
let guess_candidate cs = guess_candidate' cs (M.empty)

let rec isnt_valid z3_env cs pcandi =
  match cs with
  |(env, e1, e2 )::cs' -> (* env/\e => sita*P *)
    let sita:subst = M.map (fun tlist -> and_list tlist) pcandi in
    let p = substitution sita (Implies ( (And (env,e1)), e2)) in
    let z3_p,p_s = UseZ3.convert  p in
    if UseZ3.is_valid z3_p then
      isnt_valid z3_env cs' pcandi
    else
      Some (env, e1, e2)
  |[] -> None

let rec refine z3_env pcandi c =       (* cがvalidになるようにする。 *)
  match c with
  |(env, e, Unknown (_,sita_i, i)) ->
    let sita = M.map (fun tlist -> and_list tlist) pcandi in
    let qs = M.find i pcandi in
    let qs' = List.filter
                (fun q ->let q' = substitution sita_i q in
                         let p = substitution sita (Implies ((And(env,e), q'))) in
                         let z3_p,p_s = UseZ3.convert p in
                         UseZ3.is_valid z3_p)
                qs
    in
    M.add i qs' pcandi
  |_ -> raise (PredicateNotExist "can't refine")
    
                       

let rec iter_weak z3_env pcandi cs =
  match isnt_valid z3_env cs pcandi with
  |None -> pcandi
  |Some c -> iter_weak z3_env (refine z3_env pcandi c) cs
  
   
(*horn節を充足する、unknown predicateの対応を返す。 *)
let f (cs:(t*t*t) list) z3_env =
  let pcandi = guess_candidate cs  in (* とりあえず候補を荒くあげる *)
  let pcandi' = iter_weak z3_env pcandi  cs in
  M.map and_list pcandi'
  
  
