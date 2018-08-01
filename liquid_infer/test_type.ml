open Syntax
open Type
open Formula

let list a r p :Type.t = TScalar (TData ("list", [a], [r]),p )
let len l :Formula.t= UF (IntS, "len",[l])
                    
let v = Var  (DataS ("list",[AnyS "a"]),(Id.valueVar_id ))
                       
let a_t_cons = TScalar (TVar (M.empty,"b"),Bool true)
let a_t_rx_cons = TScalar
               (TVar (M.empty, "b"),
                UF(BoolS,"r",[Var(AnyS "a","x"); Var(AnyS "a",Id.valueVar_id)] ))

let r_pa:pa = [("_0",AnyS "a");("_1",AnyS "a")],
           UF (BoolS,"r",[Var (AnyS "a", "_0");Var (AnyS "a","_1")])

let r_rev_pa:pa =  [("_0",AnyS "a");("_1",AnyS "a")],
                   UF (BoolS,"r",[Var (AnyS "a", "_1");Var (AnyS "a","_0")])
                 

let cons_t = (["b"],[("r",([AnyS "a";AnyS "a"],BoolS))], (* パラメタ *)
              TFun(("x",a_t_cons),
                   TFun(("xs",(list a_t_rx_cons r_pa (Bool true))),
                        list
                          a_t_cons
                          r_pa
                          (Eq (len v, Plus
                                        (len (Var (DataS ("list",[AnyS "a"]),"xs")),
                                         Int 1)
             )))))

(*-----------------------------------------input-------------------------------------- *)

let input1 = TFun(("xs",(list a_t_rx_cons r_pa (Bool true))),
                    list
                      a_t_cons
                      r_pa
                      (Eq (len v, Plus
                                    (len (Var (DataS ("list",[AnyS "a"]),"xs")),
                                     Int 1)
                 )))

(*-----------------------------------------output-------------------------------------- *)           
let a_t_rx_cons' = TScalar
                     (TVar (M.empty, "b"),
                      UF(BoolS,"r",[Var(AnyS "a","x'"); Var(AnyS "a",Id.valueVar_id)] ))
let output1 =  TFun(("xs",(list a_t_rx_cons' r_pa (Bool true))),
                    list
                      a_t_cons
                      r_pa
                      (Eq (len v, Plus
                                    (len (Var (DataS ("list",[AnyS "a"]),"xs")),
                                     Int 1)
                   )))

           
(* replace_F のテスト *)

  
let _ =
  (print_string (t2string (replace_F "x" "x'" input1)));
  assert (output1 = replace_F "x" "x'" input1)
           
           
