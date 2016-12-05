Require Import graph_inst.
Open Scope positive_scope.
Definition graph5 :=  (myGraph.addEdge (1,2) (myGraph.addEdge (1,3) (myGraph.addEdge (1,4) (myGraph.addEdge (1,5) (myGraph.addEdge (1,6) (myGraph.addEdge (1,7) (myGraph.addEdge (1,8) (myGraph.addEdge (1,9) (myGraph.addEdge (1,10) (myGraph.addEdge (1,11) (myGraph.addEdge (1,12) (myGraph.addEdge (1,13) (myGraph.addEdge (1,14) (myGraph.addEdge (1,15) (myGraph.addEdge (1,16) (myGraph.addVertex 1 (myGraph.addVertex 2 (myGraph.addVertex 3 (myGraph.addVertex 4 (myGraph.addVertex 5 (myGraph.addVertex 6 (myGraph.addVertex 7 (myGraph.addVertex 8 (myGraph.addVertex 9 (myGraph.addVertex 10 (myGraph.addVertex 11 (myGraph.addVertex 12 (myGraph.addVertex 13 (myGraph.addVertex 14 (myGraph.addVertex 15 (myGraph.addVertex 16 (myGraph.addVertex 17 (myGraph.addVertex 18 (myGraph.addVertex 19 (myGraph.addVertex 20 myGraph.empty))))))))))))))))))))))))))))))))))).

Definition test1 := myGraph.Vertices.elements (myGraph.neighborhood 1 graph5).

(* Extract Constant run => *)
(*   "(fun _ p->   *)
(*      let rec int_of_pos p =  *)
(*        (match p with  *)
(*          | XH -> 1 *)
(*          | XO p' -> 2 * int_of_pos p' *)
(*          | XI p' -> (2 * int_of_pos p') + 1) *)
(*      in let rec printer l = *)
(*          (match l with *)
(*            | [] -> Printf.printf "" ""      *)
(*              |  (h:: t) -> Printf.printf ""%d "" h; printer t)         *)
(*              in printer (List.map int_of_pos (test1)". *)

Extraction "test.ml"  test1.

