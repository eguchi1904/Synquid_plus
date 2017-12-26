open Syntax
open Type
open Formula
let rec_fun f x e =  PF
                       (PFix
                          (f,
                           (PFun (x,e))))

let pmatch e cases = PI (PMatch (e,cases))

let a_t = TAny "a"
let r_pa:pa = [("_0",AnyS "a");("_1",AnyS "a")],
           UF (BoolS,"r",[Var (AnyS "a", "_0");Var (AnyS "a","_1")])

let r_rev_pa:pa =  [("_0",AnyS "a");("_1",AnyS "a")],
           UF (BoolS,"r",[Var (AnyS "a", "_1");Var (AnyS "a","_0")])
  
         
let list a r p :Type.t = TScalar (TData ("list", [a], [r]),p )
let len l :Formula.t= UF ((DataS ("list",[AnyS "a"])),
                          "len",[l])

let v = Var  (DataS ("list",[AnyS "a"]),(Id.valueVar_id ))
let cons_t = (["a"],[("r",([AnyS "a";AnyS "a"],BoolS))], (* パラメタ *)
              TFun(("x",a_t),
                   TFun(("xs",(list a_t r_pa (Bool true))),
                        list
                          a_t
                          r_pa
                          (Eq (len v, Plus
                                        (len (Var (DataS ("list",[AnyS "a"]),"xs")),
                                         Int 1)
                              )))))

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
                      (list a_t r_rev_pa   (Eq (len v,
                                                (len (Var (DataS ("list",[AnyS "a"]),"l1"))))
                                           )
               )))

let env:env = ([("Nil",nil_t);("Cons",cons_t)],[])
  
              
                                       
         
let z3_env = UseZ3.mk_z3_env ()
        
        
                               


let _ =
  (Printexc.record_backtrace true);
  let g_list = Step2.f env tmp t z3_env in
  List.iter
    (fun (g_i, env, g_t) ->
      (print_string (env2string env));
      print_string (t2string g_t);
      Printf.printf "\n\n\n")
  g_list
     


