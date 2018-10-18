OCAMLFLAGS +=  -linkpkg -bin-annot -g 



PACKS = z3



# SOURCES = extensions.ml m.ml list_map.ml s.ml id.ml syntax.ml formula.ml formula_eq.ml deformation.ml useZ3.ml find_unknownP.ml \
# type.ml preSyntax.ml data_info.mli data_info.ml  mk_tmp.ml parser.mly lexer.mll preprocess.ml\
#  ml.mli ml.ml taSyntaxl.mli taSyntax.ml typeInfer.mli typeInfer.ml\
#  main.ml 
# RESULT = liquid_infer


SOURCES = extensions.ml m.ml list_map.ml s.ml id.ml syntax.ml formula.ml formula_eq.ml \
deformation.ml useZ3.ml find_unknownP.ml \
type.ml  preSyntax.ml data_info.mli data_info.ml  mk_tmp.ml parser.mly lexer.mll preprocess.mli preprocess.ml\
taSyntax.mli taSyntax.ml ml.mli ml.ml qualifier.mli qualifier.ml typeInfer.mli typeInfer.ml \
step2.ml qe.ml step3.ml  main.ml 
RESULT = main



include OCamlMakefile


