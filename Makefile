OCAMLFLAGS +=  -linkpkg -bin-annot -g



PACKS = Z3


#SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml \
#preSyntax.ml parser.mly lexer.mll  preprocess.ml main.ml


# RESULT = syn_plus
# SOURCES = m.ml s.ml id.ml syntax.ml formula.ml l useZ3.ml find_unknownP.ml \
# type.ml preSyntax.ml parser.mly lexer.mll preprocess.ml step2.ml\
# qe.ml step3.ml main.ml 


# RESULT = step2_test
# SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml step2.ml test_step2.ml

# TYPE_TEST = type_test
#  SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml step2.ml test_type.ml


SOURCES = extensions.ml m.ml list_map.ml s.ml id.ml syntax.ml formula.ml formula_eq.ml deformation.ml useZ3.ml find_unknownP.ml \
type.ml preSyntax.ml data_info.ml  mk_tmp.ml parser.mly lexer.mll preprocess.ml step2.ml\
qe.ml step3.ml main.ml 
RESULT = our_method




include OCamlMakefile


