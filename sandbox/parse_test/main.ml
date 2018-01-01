open Syntax
let _ =
  let lexbuf = Lexing.from_channel stdin in
  let (env, fundecs, l) = Parser.toplevel Lexer.main lexbuf in
  (Printf.printf "%s\n\n%s\n\n" (env2string env) (env2string fundecs) );
  Printf.printf "[%s]" (String.concat ", " l)
                                              
