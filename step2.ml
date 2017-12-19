open Syntax


  
  
                
let rec f (env:Env.t) (e:Syntax.t) (t:Type.t) =
  match e  with
  |PE(PSymbol v) -> []          (* とりあえず型検査しない *)
  |PE(PAuxi g) -> [(g,(env,t))]
  |PE(PAppFo (e1,e2)) ->
    let t2 = inferETerm env e2 in
    let x = Id.genid "x" in
    f env (PE e1) (Type.FunT ((x,t2),t))

    
