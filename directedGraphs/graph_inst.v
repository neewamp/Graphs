Require Import DirectedGraphs.
Require Import MSets MSetFacts.

Module myGraph : DirectedGraphs.
  
  Require Import MSetAVL.
  Require Import ZArith.
  Module pos :=  PositiveOrderedTypeBits.
  
  Module Vertices := MSetAVL.Make pos.
  Definition node := pos.t.
  Module Edge := PairOrderedType pos pos.
  Module Edges := MSetAVL.Make Edge.


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
     forall G : t, IsEmpty G -> Vertices.Empty (enumVertices G).
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
        (Vertices.mem (fst e) (graphVertices G) &&
                      Vertices.mem (snd e) (graphVertices G) = true) ->
        ok (graphVertices G) (Edges.add e (graphEdges G)).
    Proof.
      intros.
      apply andb_true_iff in H.
      unfold ok.
      intros.
      apply Edges.add_spec in H0.
      destruct H0.
      rewrite  H0.
      do 2 rewrite Vertices.mem_spec in H.
      auto.
      destruct G.
      simpl in *.
      specialize (graphOk0 e0 H0).
      auto.
    Qed.

    Definition addEdge (e : edge) (G : t) :t.
      case_eq (Vertices.mem (fst e) (graphVertices G) &&
                            Vertices.mem (snd e) (graphVertices G)).
      intros.
      exact (mkgraph (graphVertices G)
                     (Edges.add e (graphEdges G)) (add_ok e G H)).
      intros _.
      exact G.
    Defined.

    Program Definition addEdge' (e : edge) (G : t) : t :=
      match (Vertices.mem (fst e) (graphVertices G) &&
             Vertices.mem (snd e) (graphVertices G)) with
      | true => mkgraph (graphVertices G)
                        (Edges.add e (graphEdges G))
                        (add_ok e G _)
      | false => G
      end.


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
    
    (*This is either wrong or could be written better*)
    Lemma addEdge_does_something : forall e G G1,
        (addEdge e G) = G1 ->                                                  (~(Vertices.In (fst (destructEdge e)) (graphVertices G) /\
       Vertices.In (snd (destructEdge e)) (graphVertices G)) /\ G1 = G)                    \/ Edges.In e (graphEdges G1).
    Proof.
      intros.
      unfold not;intros.
      destruct addEdge in H.
      right.
      unfold ok in graphOk0.
      unfold graphEdges.
      destruct G1.
    Admitted.
    
    Lemma addEdge_spec1 :
      forall G e,
        IsVertex (fst (destructEdge e)) G->
        IsVertex (snd (destructEdge e)) G->
        IsEdge e (addEdge' e G).
    Proof.
      intros G e H H1.
      unfold addEdge'.
      elimtype.
      inversion.
    Qed.

  Lemma addEdge_spec2 :
    forall G e1 e2, e1 <e> e2 ->
                    IsEdge e1 G <-> IsEdge e1 (addEdge e2 G).
  Proof.
    intros.
    split;
    intros.
    unfold IsEdge in *.
    unfold graphEdges in *.
    destruct (addEdge e2 G) eqn:H1.
    destruct G.
    (* specialize (graphOk0 e1 H0). *)
    Admitted.

  Lemma addEdge_spec3 : forall G v e,
    IsVertex v G <-> IsVertex v  (addEdge e G).
  Proof.
    Admitted.

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
  (* ~Vertices.E.eq v1 v2 *)
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

    Parameter removeVertex_spec4 :
    forall G v e,
      IsEdge e G ->
        (fst (destructEdge e) =v= v) \/
        (snd (destructEdge e) =v= v) ->
          ~ IsEdge e (removeVertex v G).
    (*   intros G v e H H0 Hnot. *)
    (*   destruct e. *)
    (*   simpl in *. *)
    (*   destruct H0; *)
    (*   unfold IsEdge in Hnot. *)
    (*   apply Edges.filter_spec in Hnot. *)
    (*   destruct Hnot. *)
    (*   apply andb_true_iff in H2. *)
    (*   do 2 rewrite negb_true_iff in H2. *)
    (*   destruct H2. *)
    (*   rewrite Pos.eqb_neq in H2,H3. *)
    (*   auto. *)
    (*   apply annoyingProper. *)
    (*   apply Edges.filter_spec in Hnot. *)
    (*   destruct Hnot. *)
    (*   apply andb_true_iff in H2. *)
    (*   do 2 rewrite negb_true_iff in H2. *)
    (*   destruct H2. *)
    (*   rewrite Pos.eqb_neq in H2,H3. *)
    (*   auto. *)
    (*   apply annoyingProper. *)
    (* Qed. *)
      (* Admitted. *)
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
    Compute enumEdges g.
    

End myGraph.  
  

  

