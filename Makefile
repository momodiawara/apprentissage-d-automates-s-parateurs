apprentissage: apprentissage.ml
	ocamlfind ocamlopt -o apprentissage -linkpkg apprentissage.ml

%.smt2: %.dat apprentissage
	./apprentissage $< > $@

test: input_1.smt2 input_2.smt2
	z3 input_1.smt2
	z3 input_2.smt2

clean:
	rm -f *~ *.cmi *.cmx *.o apprentissage *.smt2
