all:
	cp ../directedGraphs/DirectedGraphs.v ../directedGraphs/DirectedGraphs_morph.v ../directedGraphs/graph_inst.v .
	coqc DirectedGraphs.v DirectedGraphs_morph.v graph_inst.v
	g++ -o builder makegraph.cc 

compile:
	coqc DirectedGraphs.v DirectedGraphs_morph.v graph_inst.v	

ocompile:
	ocamlbuild test.native


clean:
	-rm *.vo
	-rm *.glob
	-rm *~
	-rm builder
	-rm -r _build
	-rm *test.*
	-rm a.out
