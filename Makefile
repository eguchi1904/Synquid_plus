OCAMLFLAGS +=  -linkpkg -bin-annot

RESULT = syn_plus

PACKS = Z3

SOURCES = m.ml s.ml id.ml syntax.ml formula.ml useZ3.ml find_unknownP.ml  type.ml


include OCamlMakefile


