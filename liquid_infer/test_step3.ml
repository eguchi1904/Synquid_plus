open Syntax
open Type
open Formula
let rec_fun f x e =  PF
                       (PFix
                          (f,
                           (PFun (x,e))))

let pmatch e cases = PI (PMatch (e,cases))

let a_t = TScalar (TVar (M.empty,"a"),Bool true)
let a_t_rx = TScalar
               (TVar (M.empty, "a"),
                UF(BoolS,"r",[Var(AnyS "a","x"); Var(AnyS "a",Id.valueVar_id)] )
               )


                                 
let r_pa:pa = [("_0",AnyS "a");("_1",AnyS "a")],
           UF (BoolS,"r",[Var (AnyS "a", "_0");Var (AnyS "a","_1")])

let r_rev_pa:pa =  [("_0",AnyS "a");("_1",AnyS "a")],
           UF (BoolS,"r",[Var (AnyS "a", "_1");Var (AnyS "a","_0")])
  
         
let list a r p :Type.t = TScalar (TData ("list", [a], [r]),p )
let len l :Formula.t= UF (IntS, "len",[l])
let any_set_sort = SetS (AnyS "a")
let any_list_sort = DataS("list",[AnyS "a"])
let elems x = UF (any_set_sort, "elems", [Var(any_list_sort, x)])



let a_t_cons = TScalar (TVar (M.empty,"b"),Bool true)
let a_t_rx_cons = TScalar
               (TVar (M.empty, "b"),
                UF(BoolS,"r",[Var(AnyS "a","x"); Var(AnyS "a",Id.valueVar_id)] )
               )
let v = Var  (DataS ("list",[AnyS "a"]),(Id.valueVar_id ))                
let cons_t = (["b"],[("r",([AnyS "a";AnyS "a"],BoolS))], (* パラメタ *)
              TFun(("x",a_t_cons),
                   TFun(("xs",(list a_t_rx_cons r_pa (Bool true))),
                        list
                          a_t_cons
                          r_pa
                       (And (
                          (Eq (len v, Plus
                                        (len (Var (DataS ("list",[AnyS "a"]),"xs")),
                                         Int 1))
                          ),
                          (Eq (elems Id.valueVar_id,
                               (Union (elems "xs",
                                       (Set (AnyS "a",[Var(AnyS "a", "x")]))
                                      )
                               )
                          ))
                          )
                       )
                       )))





let nil_t =  (["a"],[("r",([AnyS "a";AnyS "a"],BoolS))], (* パラメタ *)
              list a_t r_rev_pa  (Eq (len v,Int 0)))

let list_v l = Var (DataS ("list",[AnyS "a"]), l)

let match_body = PE (PAppFo
                       (PAppFo (PAuxi "snoc",PSymbol "x'"),
                        PAppFo (PSymbol "f", PSymbol "xs'")))
                    

               
                             

        



let tmp = rec_fun "f" "l"
                  (pmatch (PSymbol "l")
                  [{constructor="Nil";argNames=[];body = PHole};
                   {constructor="Cons";argNames=["x'";"xs'"];body =match_body }])


let t:schema = (["a"],[("r",([AnyS "a";AnyS "a"],BoolS))], (* パラメタ *)
                TFun (("l1",(list a_t r_pa (Bool true))),
                      (list a_t r_rev_pa
                            (And (Eq (len v,
                                       (len (Var (DataS ("list",[AnyS "a"]),"l1")))
                                     ),
                                  Eq (elems Id.valueVar_id,
                                      elems "l1"))
                            )
                      )))
             
let env:env = ([("Nil",nil_t);("Cons",cons_t)],[])
  
              
                                       
         
let z3_env = UseZ3.mk_z3_env ()  
let _ =
  let g_list = Step2.f env tmp t z3_env in
    (List.iter
    (fun (g_i, env, g_t) ->
      (Printf.printf "auxi:%s\n" g_i);
        (print_string (env2string env));
      print_string (t2string g_t);
      Printf.printf "\n\n\n")
    g_list
  );
  let g_list = List.map
                 (fun (g_name,g_env,g_t) ->
                   (g_name, Step3.f g_name g_env g_t))
                 g_list
  in

  List.iter
    (fun (g_name,g_t) ->
      (Printf.printf "auxi:%s\n" g_name);
      print_string (t2string g_t);
      Printf.printf "\n\n\n")
  g_list
  


