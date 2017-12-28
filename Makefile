OCAMLFLAGS +=  -linkpkg -bin-annot -g

RESULT = syn_plus

PACKS = Z3

SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml step2.ml\
qe.ml step3.ml test_step3.ml

# RESULT = step2_test
# SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml step2.ml test_step2.ml

# TYPE_TEST = type_test
#  SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml step2.ml test_type.ml

include OCamlMakefile


