Require Import DirectedGraphs Ascii ExtrOcamlString.
Require Import MSets MSetFacts PArith DirectedGraphs_morph.

Module myGraph <: DirectedGraphs.
  
  Require Import MSetRBT.
  Require Import ZArith.
  Module pos :=  PositiveOrderedTypeBits.
  
  Module Vertices := MSetRBT.Make pos.
  Definition node := pos.t.
  Module Edge := PairOrderedType pos pos.
  Module Edges := MSetRBT.Make Edge.


  Module vert_facts := WFacts (Vertices).
  Module edge_facts := WFacts (Edges).
  Module vert_prop := WProperties (Vertices).
  Module edge_prop := WProperties (Edges).

  Definition edge := Edges.elt.
  Definition v_set := Vertices.t.
  Definition e_set := Edges.t.
  
  Definition ok  (V : v_set) (E : e_set) : Prop :=
    forall (e : edge), Edges.In e E ->
                       (Vertices.In (fst e) V) /\ (Vertices.In (snd e) V). 

  Record Graph :=
    mkgraph {
        graphVertices: v_set; 
        graphEdges : e_set;
        graphOk : ok graphVertices graphEdges
      }.
  
  Notation vertex := Vertices.elt.
  
  Definition buildEdge (n n1 : vertex): Edges.elt :=
    (n,n1).

  Definition t := Graph.

  Open Scope positive_scope.

  Program Definition empty := mkgraph Vertices.empty Edges.empty _.
  Next Obligation.
    unfold ok.
    intros.
    inversion H.
  Qed.
  
  Definition buildPair : vertex -> vertex -> vertex * vertex :=
    fun x y => (x,y).

  Definition destructEdge : Edge.t -> (vertex * vertex) :=
    fun X : Edge.t => let (p, p0) := X in (p, p0).

  Definition isemptyP : v_set -> e_set -> Prop :=
    fun (x : v_set) (y : e_set) => Vertices.Empty x  /\ Edges.Empty y.

  Definition  IsEmpty : Graph -> Prop :=
    fun G : Graph =>
      Vertices.Empty (graphVertices G) /\ Edges.Empty (graphEdges G).

  Definition IsVertex : Vertices.elt -> Graph -> Prop :=
    fun (n : Vertices.elt) (G : Graph)  =>
      Vertices.In n (graphVertices G).

  Definition IsEdge : Edges.elt -> Graph -> Prop :=
    fun (e : Edges.elt) (G : Graph) => 
      Edges.In e (graphEdges G).

  Definition isEmpty : Graph -> bool :=
    fun (G : Graph) => andb (Vertices.is_empty (graphVertices G))
                            (Edges.is_empty (graphEdges G)).

  Definition isVertex : Vertices.elt -> Graph -> bool :=
    fun (v : Vertices.elt) (G : Graph)  =>
      Vertices.mem v (graphVertices G).

  Definition isEdge : Edges.elt -> Graph -> bool :=
    fun (e : Edges.elt) (G : Graph) =>
      Edges.mem e (graphEdges G).

  Lemma IsEmpty_reflect :
    forall G : Graph, reflect (IsEmpty G) (isEmpty G).
  Proof.
    intros.
    unfold IsEmpty.
    unfold isEmpty.
    destruct G.
    apply iff_reflect.
    rewrite <- Vertices.is_empty_spec.
    rewrite <- Edges.is_empty_spec.
    split; intros; try apply andb_true_iff; auto.
  Qed.

  Lemma IsVertex_reflect :
    forall (G : Graph) (v : node),
      reflect (IsVertex v G) (isVertex v G).
  Proof.
    intros.
    destruct G.
    simpl.
    apply iff_reflect.
    split; intros; try apply Vertices.mem_spec; auto.
  Qed.

  Lemma IsEdge_reflect :
    forall (G : Graph) (e : Edges.elt), reflect (IsEdge e G) (isEdge e G).
  Proof.
    intros.
    destruct G.
    apply iff_reflect.
    unfold IsEdge, isEdge.
    split; try apply Edges.mem_spec; auto.
  Qed.
  
  Definition enumVertices : Graph -> Vertices.t :=
    fun (g : Graph) => graphVertices g.
  
  Definition enumEdges : Graph -> Edges.t :=
    fun (G : Graph) => (graphEdges G).

  Lemma Empty : IsEmpty empty.
  Proof.
    unfold empty.
    unfold IsEmpty.
    split.
    apply Vertices.empty_spec.
    apply Edges.empty_spec.
  Qed.
  
  Lemma Empty_vertices :
    forall G : Graph, IsEmpty G -> Vertices.Empty (enumVertices G).
  Proof.
    intros.
    destruct G.
    simpl in *.
    destruct H.
    auto.
  Qed.
  
  Lemma Empty_edges :
    forall G : t, IsEmpty G -> Edges.Empty (enumEdges G).
  Proof.
    intros [V E] H. simpl in *; destruct H.
    auto.
  Qed.

  Lemma IsVertexEnum :
    forall (G : t) (v : Vertices.elt),
      IsVertex v G <-> Vertices.In v (enumVertices G).
  Proof.
    intros [V E] v; split; simpl; intros; auto.
  Qed.

  Lemma IsEdgeEnum :
    forall (G : t) (e : Edges.elt), IsEdge e G <-> Edges.In e (enumEdges G).
  Proof.
    intros [V E] v; split; simpl; intros; auto.
  Qed.

  Lemma Edge_exists1 :
    forall (G : t) (e : Edges.elt),
      IsEdge e G -> IsVertex (fst (destructEdge e)) G.
  Proof.
    intros G e H.
    unfold destructEdge.
    destruct G.
    unfold IsVertex.
    unfold IsEdge in H.
    simpl in *.
    specialize (graphOk0 e H).
    destruct e.
    apply graphOk0.
  Qed.


  Lemma Edge_exists2 :
    forall G e, IsEdge e G -> IsVertex (snd (destructEdge e)) G.
  Proof.
    intros.
    unfold destructEdge, IsVertex, IsEdge in *.
    destruct G.
    simpl in *.
    specialize (graphOk0 e H).
    destruct e.
    apply graphOk0.
  Qed.

  Program Definition addVertex  (v : vertex) (G : t) : t :=
    mkgraph (Vertices.add v (graphVertices G)) (graphEdges G) _.
  Next Obligation.
    destruct G.
    unfold ok in *.
    simpl.
    intros.
    specialize (graphOk0 e H).
    split;
      apply Vertices.add_spec;
      right;
      apply graphOk0.
  Qed.

  Lemma add_ok : forall e G,
      Vertices.In (fst e) (graphVertices G) ->
      Vertices.In (snd e) (graphVertices G) ->
      ok (graphVertices G) (Edges.add e (graphEdges G)).
  Proof.
    unfold ok.
    intros. apply Edges.add_spec in H1;
              destruct e; destruct e0;
                destruct H1.
    inversion H1;  inversion H2; inversion H3; simpl in *; auto.
    simpl.
    destruct G.
    simpl in *.
    specialize (graphOk0 _ H1).
    auto.
  Qed.

  Lemma Vertices_in_dec1 : forall (e : vertex*vertex) G,
      {Vertices.In (fst e) (graphVertices G)} +
      {~ Vertices.In (fst e) (graphVertices G)}.
  Proof.
    intros.
    case_eq (Vertices.mem (fst e) (graphVertices G));
      intros H.
    rewrite Vertices.mem_spec in H; left; auto.
    right; intros H1. rewrite <- Vertices.mem_spec in H1.
    rewrite H in H1. inversion H1.
  Qed.

  Lemma Vertices_in_dec2 : forall (e : vertex*vertex) G,
      {Vertices.In (snd e) (graphVertices G)} +
      {~ Vertices.In (snd e) (graphVertices G)}.
  Proof.
    intros.
    case_eq (Vertices.mem (snd e) (graphVertices G));
      intros H.
    rewrite Vertices.mem_spec in H; left; auto.
    right; intros H1. rewrite <- Vertices.mem_spec in H1.
    rewrite H in H1. inversion H1.
  Qed.

  Lemma Vertices_in_dec : 
    forall (e : vertex*vertex) G,
      {Vertices.In (fst e) (graphVertices G) /\
       Vertices.In (snd e) (graphVertices G)} +
      {~ (Vertices.In (fst e) (graphVertices G) /\
          Vertices.In (snd e) (graphVertices G))}.
  Proof.
    intros.
    destruct (Vertices_in_dec1 e G);
      destruct (Vertices_in_dec2 e G);
      [left; auto | right | right | right]; intros H;
        destruct H; auto.
  Qed.

  Program Definition addEdge (e : edge) (G : t) : t :=
    if (Vertices_in_dec e G)
    then mkgraph (graphVertices G)
                 (Edges.add e (graphEdges G))
                 _
    else G.
  Next Obligation.
  Proof.
    apply add_ok; auto.
  Defined.

  Lemma annoyingProper : forall v,
      Proper (eq * eq ==> eq)
             (fun x : Edges.elt => negb (fst x =? v) && negb (snd x =? v)).
  Proof.
    unfold Proper.
    unfold respectful.
    intros v x y H.
    destruct H.
    rewrite H,H0.
    auto.
  Qed.

  Notation "V1 =V= V2" := (Vertices.eq V1 V2) (at level 60).
  Notation "V1 <V> V2" := (~ Vertices.eq V1 V2) (at level 60). 
  Notation "E1 =E= E2" := (Edges.eq E1 E2) (at level 60).
  Notation "E1 <E> E2" := (~ Edges.eq E1 E2) (at level 60). 
  Notation "v1 =v= v2" := (Vertices.E.eq v1 v2) (at level 60).
  Notation "v1 <v> v2" := (~ Vertices.E.eq v1 v2) (at level 60). 
  Notation "e1 =e= e2" := (Edges.E.eq e1 e2) (at level 60).
  Notation "e1 <e> e2" := (~ Edges.E.eq e1 e2) (at level 60). 


  Program Definition removeVertex  (v : vertex) (G : t) : t :=
    let newE := Edges.filter (fun x => (negb (Pos.eqb (fst x) v)) &&  negb (Pos.eqb (snd x)  v)) (graphEdges G) in
    mkgraph (Vertices.remove v (graphVertices G)) (newE) _.
  Next Obligation.
    intros e H.
    destruct G.
    simpl in *.
    unfold ok in graphOk0.
    apply Edges.filter_spec in H.
    destruct H.
    apply andb_true_iff in H0.
    destruct H0.
    rewrite negb_true_iff in H1,H0.
    rewrite Pos.eqb_neq in H0,H1.
    split;
      apply vert_prop.Dec.F.remove_2;
      auto;
      try apply graphOk0;
      auto.
    apply annoyingProper.
  Defined.

  Program Definition removeEdge  (e : edge) (G : t) : t :=
    mkgraph (graphVertices G) (Edges.remove e (graphEdges G)) _.
  Next Obligation.
    intros e1 H.
    destruct G.
    simpl in *.
    apply graphOk0.
    apply Edges.remove_spec in H.
    apply H.
  Defined.

  Lemma addVertex_spec1 :
    forall G v, IsVertex v (addVertex v G).
  Proof.
    intros [V G pf] v.
    unfold IsVertex.
    simpl.
    apply Vertices.add_spec.
    auto.
  Qed.

  Lemma addVertex_spec2 :
    forall G v1 v2, ~ Vertices.E.eq v1 v2 ->
                    IsVertex v1 G <-> IsVertex v1 (addVertex v2 G).
  Proof.
    intros [V E pf] v1 v2 H. 
    unfold IsVertex.
    simpl.
    unfold not in H.
    split; intros; auto.
    apply Vertices.add_spec.
    auto.
    apply Vertices.add_spec in H0.
    destruct H0; auto.
    apply H in H0.
    destruct H0.
  Qed.

  Lemma addVertex_spec3 :
    forall G v e,
      IsEdge e G <-> IsEdge e (addVertex v G).
  Proof.
    intros [V E pf] v e.
    unfold IsEdge.
    simpl.
    split; intros; auto.
  Qed.
  
  Lemma addEdge_spec1 :
    forall G e,
      IsVertex (fst (destructEdge e)) G->
      IsVertex (snd (destructEdge e)) G->
      IsEdge e (addEdge e G).
  Proof.
    intros G e. unfold addEdge; intros.
    destruct (Vertices_in_dec e G).
    unfold IsEdge.
    simpl.
    apply Edges.add_spec.
    auto.
    unfold IsVertex in *.
    destruct e.
    unfold not in n.
    assert (False).
    apply n.
    auto.
    destruct H1.
  Qed.
  
  Lemma addEdge_spec2 :
    forall G e1 e2, e1 <e> e2 ->
                    IsEdge e1 G <-> IsEdge e1 (addEdge e2 G).
  Proof.
    intros.
    split; unfold addEdge; intros; unfold IsEdge; simpl.
    destruct (Vertices_in_dec e2 G).
    simpl.
    apply Edges.add_spec.
    auto.
    auto.
    unfold graphEdges.
    destruct G.
    simpl in *.
    destruct (Vertices_in_dec e2) in H0.
    simpl in *.
    unfold IsEdge in H0.
    simpl in H0.
    apply Edges.add_spec in H0.
    destruct H0; auto.
    unfold not in H.
    assert (False).
    apply H.
    auto. destruct H1.
    auto.
  Qed.


  Lemma addEdge_spec3 : forall G v e,
      IsVertex v G <-> IsVertex v  (addEdge e G).
  Proof.
    intros.
    split; unfold IsVertex, addEdge; intros.
    destruct (Vertices_in_dec e G).
    simpl.
    auto.
    auto.
    destruct (Vertices_in_dec e G) in H; auto.
  Qed.

  Lemma removeVertex_spec1 :
    forall G v, ~ IsVertex v (removeVertex v G).
  Proof.
    intros G v H.
    unfold IsVertex in H.
    simpl in H.
    apply Vertices.remove_spec in H.
    destruct H.
    unfold not in H0.
    auto.
  Qed.

  Lemma removeVertex_spec2 :
    forall G v1 v2, v1 <v> v2 ->
                    IsVertex v1 G <-> IsVertex v1 (removeVertex v2 G).
  Proof.
    intros G v1 v2 H.
    split;
      intros H0;
      unfold IsVertex in *;
      simpl in *;
      try apply vert_prop.Dec.F.remove_2;
      try apply vert_prop.Dec.F.remove_3 in H0;
      auto.
  Qed.


  Lemma removeVertex_spec3 :
    forall G v e,
      IsEdge e (removeVertex v G) <->
      IsEdge e G /\
      (fst (destructEdge e)) <v> v /\
      (snd (destructEdge e)) <v> v.
  Proof.
    intros G v e.
    unfold IsEdge.
    split; intros H.
    {
      split.
      unfold graphEdges in *.
      destruct G.
      simpl in *.
      apply Edges.filter_spec in H.
      apply H.
      apply annoyingProper.
      unfold destructEdge.
      destruct e.
      simpl.
      unfold removeVertex in H.
      simpl in H.
      apply Edges.filter_spec in H.
      destruct H.
      apply andb_true_iff in H0.
      destruct H0.
      simpl in *.
      rewrite negb_true_iff in H0,H1.
      rewrite Pos.eqb_neq in H0,H1.
      auto.
      apply annoyingProper.
    }
    {
      destruct H.
      destruct H0.
      destruct e.
      simpl in H,H0,H1.
      apply Edges.filter_spec.
      apply annoyingProper.
      split.
      auto.
      apply andb_true_iff.
      do 2 rewrite negb_true_iff.
      simpl.
      do 2  rewrite Pos.eqb_neq.
      auto.
    }
  Qed.

  Lemma my_neg_iff_prop : forall p p0 v,
      negb (fst (p, p0) =? v) && negb (snd (p, p0) =? v) = true ->
      fst (p, p0) <> v /\  snd (p, p0) <> v .
  Proof.
    intros.
    simpl in *.
    apply andb_true_iff in H.
    destruct H.
    rewrite negb_true_iff in H, H0.
    rewrite Pos.eqb_neq in H,H0.
    auto.
  Qed.

  Lemma  removeVertex_spec4 :
    forall G v e,
      IsEdge e G ->
      (fst (destructEdge e) =v= v) \/
      (snd (destructEdge e) =v= v) ->
      ~ IsEdge e (removeVertex v G).
    intros G v e H H0 Hnot.
    destruct e.
    simpl in *.
    destruct H0;
      unfold IsEdge in Hnot.
    apply Edges.filter_spec in Hnot.
    destruct Hnot.
    apply andb_true_iff in H2.
    do 2 rewrite negb_true_iff in H2.
    destruct H2.
    rewrite Pos.eqb_neq in H2,H3.
    auto.
    apply annoyingProper.
    apply Edges.filter_spec in Hnot.
    destruct Hnot.
    apply andb_true_iff in H2.
    do 2 rewrite negb_true_iff in H2.
    destruct H2.
    rewrite Pos.eqb_neq in H2,H3.
    auto.
    apply annoyingProper.
  Qed.

  Lemma removeEdge_spec1 :
    forall G e, ~ IsEdge e (removeEdge e G).
  Proof.
    intros G e Hnot.
    unfold IsEdge in Hnot.
    simpl in Hnot.
    apply edge_prop.Dec.F.remove_1 in Hnot.
    destruct Hnot.
    auto.
  Qed.

  Lemma removeEdge_spec2 :
    forall G e1 e2, e1 <e> e2 -> 
                    IsEdge e1 G <-> IsEdge e1 (removeEdge e2 G).
  Proof.
    intros G e1 e2 H.
    unfold IsEdge.
    split; intros H0; auto.
    simpl.
    apply edge_prop.Dec.F.remove_2.
    intros Hnot.
    destruct Hnot.
    unfold not in H.
    apply H.
    constructor; auto.
    auto.
    unfold graphEdges in *.
    simpl in *.
    destruct G.
    simpl in *. 
    apply Edges.remove_spec in H0.
    destruct H0.
    auto.
  Qed.
  Lemma removeEdge_spec3 :
    forall G v e,
      IsVertex v G <-> IsVertex v (removeEdge e G).
  Proof.
    reflexivity.
  Qed.

  Definition g := addEdge (1,3) (addVertex 3 (addVertex 1 empty)).
  
  Definition graph1 :=  (addEdge (1,2) (addEdge (1,3) (addVertex 1 (addVertex 2 (addVertex 3 (addVertex 4 (addVertex 5 empty))))))).
  
  Definition graph2 :=  (addEdge (1,2) (addEdge (1,3) (addVertex 1 (addVertex 2 (addVertex 3 (addVertex 4 (addVertex 5 empty))))))).

  Definition neighborhood (v : vertex) (G : t): Vertices.t :=
    Edges.fold (fun edge e =>
                  if Pos.eqb (fst edge) v then Vertices.add (snd edge) e
                  else e) (enumEdges G) Vertices.empty.
  Definition test := map ascii_of_pos (Vertices.elements (neighborhood 1 graph2)).
  Require Import List.
  

  Definition graph_contains (x : vertex) (g : t) : bool :=
    Vertices.mem x (graphVertices g).

  Definition graph_Contains (x : vertex)  (g: t) : Prop :=
    Vertices.In x (graphVertices g).
  

  Lemma graph_containsP : forall x g,
      reflect (graph_Contains x g) (graph_contains x g).
  Proof.
    intros.
    apply iff_reflect.
    unfold graph_Contains, graph_contains.
    split; intros H; apply Vertices.mem_spec; auto.
  Qed.

  Definition isNeighbor (x y : vertex) (g : t) : Prop :=
    Edges.In (x,y) (graphEdges g).
  
  Inductive path (g : t) : node -> node -> list node -> Prop :=
  | start : forall x, graph_Contains x g -> path g x x (x::nil)
  | step  : forall x y z l,
      graph_Contains x g ->
      path g y z (y::l) ->
      isNeighbor x y g ->
      path g x z (x::y::l).

  
End myGraph.

Module g_prop :=  DirectedGraphMorph myGraph.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].
(* Extract Inductive positive => int [ "XI" "XO" "XH" ] *)
(*    "let rec int_of_pos p = *)
(*   (match p with *)
(*    |XH -> 1 *)
(*    |XO p' -> 2 * (int_of_pos p') *)
(*    |XI p' -> 2* (int_of_pos p') + 1)". *)
(* Extraction "myGraph.ml"  myGraph. *)

  

