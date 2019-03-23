OCAMLFLAGS +=  -linkpkg -bin-annot
#OCAMLLDFLAGS += -ccopt -I,"~/.opam/ocaml-base-compiler.4.06.1/.opam-switch/sources/z3.4.8.1/src/api"
#EXTLIBDIRS =  ~/.opam/4.06.1/lib/z3/
OCAMLLDFLAGS += -thread -ccopt -Wl,-rpath,"/Users/eguchishingo/.opam/ocaml-base-compiler.4.06.1/lib/z3"



PACKS = Z3 Ocamlgraph



# SOURCES = extensions.ml m.ml list_map.ml s.ml id.ml syntax.ml formula.ml formula_eq.ml deformation.ml useZ3.ml find_unknownP.ml \
# type.ml preSyntax.ml data_info.mli data_info.ml  mk_tmp.ml parser.mly lexer.mll preprocess.ml\
#  ml.mli ml.ml taSyntaxl.mli taSyntax.ml typeInfer.mli typeInfer.ml\
#  main.ml 
# RESULT = liquid_infer


SOURCES = extensions.ml m.ml list_map.ml s.ml id.mli id.ml syntax.ml taSyntax.mli taSyntax.ml formula.mli formula.ml formula_eq.ml \
deformation.ml  qe.mli qe.ml useZ3.mli useZ3.ml find_unknownP.ml \
type.mli type.ml  preSyntax.ml data_info.mli data_info.ml  mk_tmp.ml parser.mly lexer.mll preprocess.mli preprocess.ml\
 ml.mli ml.ml qualifier.mli qualifier.ml constraint.mli constraint.ml\
consGen.mli consGen.ml consSolver.mli consSolver.ml solver.mli solver.ml typeInfer.mli typeInfer.ml\
step2.ml step3.ml  main.ml

RESULT = main



include OCamlMakefile


