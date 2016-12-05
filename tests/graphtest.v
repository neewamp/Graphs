Require Import graph_inst.
 Open Scope positive_scope.
Definition graph1 :=  (myGraph.addEdge (1,2) (myGraph.addEdge (1,3) (myGraph.addEdge (2,2) (myGraph.addVertex 1 (myGraph.addVertex 2 (myGraph.addVertex 3 (myGraph.addVertex 4 myGraph.empty))))))).
Definition test1 := myGraph.Vertices.elements (myGraph.neighborhood 1 graph1).
Extraction "test.ml" test1 .
