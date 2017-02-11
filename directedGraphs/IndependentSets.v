Require Import MSets.
Require Import SimpleUndirectedGraphs DirectedGraphs_morph.

(* If things turn out ok in this file it doesn't seem hard to
   integrate everything with maxind *)

Module independentSets (DG : SimpleUndirectedGraphs).
  Import DG.
  Module DG_Facts := DirectedGraphMorph DG.
  Module vert_prop := WProperties (Vertices).
  Module vertFacts := OrderedTypeFacts Vertices.E.
  
  (* Prop and bool definitions of an Independent Set with respect to a 
      Graph 
   *)
  Definition IndependentSet (X : Vertices.t) (G : t) :=
    forall x y, Vertices.In x X -> Vertices.In y X ->
                ~ Edges.In (buildEdge x y) (DG.enumEdges G).

  Definition independentSet (X : Vertices.t) (G : t) :=
    Vertices.for_all (fun v1 => Vertices.for_all
    (fun v2 => negb (Edges.mem (buildEdge v1 v2) (enumEdges G))) X) X.


  Lemma annoyingProperV2 : 
    forall v1 G,  Proper (Vertices.E.eq ==> eq)
     (fun v2 : vertex =>
      negb (Edges.mem (buildEdge v1 v2) (enumEdges G))).
  Proof.
    intros.
    unfold Proper.
    unfold respectful.
    intros x y H.
    erewrite buildEdge_spec; try reflexivity; 
    auto.
  Qed.

  Lemma proper_aux : forall x0 G y0 X, x0 =v= y0 ->
       Vertices.For_all
         (fun x : vertex =>
            negb (Edges.mem (buildEdge x0 x) (enumEdges G)) = true) X
  ->
Vertices.for_all
     (fun v2 : vertex =>
      negb (Edges.mem (buildEdge x0 v2) (enumEdges G))) X = true.

  Proof.
    intros.
    apply Vertices.for_all_spec.
    apply annoyingProperV2.
    unfold Vertices.For_all. intros.
    unfold Vertices.For_all in *; intros.
    apply H0 in H1.
    assert (buildEdge x0 x =e= buildEdge y0 x).
    apply buildEdge_spec; try reflexivity; auto.
    auto.
  Qed.

  Lemma proper_forall_helper : 
    forall x0 y0 X G,
      x0 =v= y0 ->
      Vertices.for_all
        (fun v2 : vertex =>
           negb (Edges.mem (buildEdge x0 v2) (enumEdges G))) X =
      Vertices.for_all
        (fun v2 : vertex =>
           negb (Edges.mem (buildEdge y0 v2) (enumEdges G))) X.
  Proof.
    intros.
    case_eq (Vertices.for_all
               (fun v2 : vertex =>
                  negb (Edges.mem (buildEdge x0 v2) (enumEdges G)))X );
      case_eq ( Vertices.for_all
                  (fun v2 : vertex =>
                     negb (Edges.mem (buildEdge y0 v2) (enumEdges G))) X);
      intros; auto.
    apply Vertices.for_all_spec in H1.
    apply not_true_iff_false in H0.
    unfold not in H0.
    exfalso; apply H0.
    apply Vertices.for_all_spec.
    apply annoyingProperV2.
    unfold Vertices.For_all.
    intros.
    apply H1 in H2.
    assert ((buildEdge x0 x) =e= (buildEdge y0 x)).
    apply buildEdge_spec; try reflexivity; auto.
    rewrite <-  H3.
    auto.
    apply annoyingProperV2.
    apply Vertices.for_all_spec in H0.
    apply not_true_iff_false in H1.
    unfold not in H1.
    exfalso; apply H1.
    apply proper_aux with (y0 := y0); auto.
    unfold Vertices.For_all.
    intros.
    apply H0 in H2.
    assert ((buildEdge x0 x) =e= (buildEdge y0 x)).
    apply buildEdge_spec; try reflexivity;
      auto.
    rewrite H3.
    auto.
    apply annoyingProperV2.
  Qed.

  (* This was very annoying I'll try and make stuff look better later *)
  Theorem independentSet_true_iff :
    forall X G,
  reflect (IndependentSet X G) (independentSet X G). 
  Proof.
    intros.
    apply iff_reflect.
    symmetry.
    unfold independentSet, IndependentSet.
    split; intros.
    intros Hnot.
    apply Vertices.for_all_spec in H.
    unfold Vertices.For_all in H.
    apply H in H0.
    apply Vertices.for_all_spec in H0.
    unfold Vertices.For_all in H0,H1.
    apply H0 in H1.
    apply Edges.mem_spec in Hnot.
    unfold negb in H1.
    rewrite Hnot in H1.
    inversion H1.
    apply annoyingProperV2.
    unfold Proper.
    unfold respectful.
    intros.
    apply proper_forall_helper.
    auto.
    apply Vertices.for_all_spec.
    unfold Proper.
    unfold respectful.
    intros.
    apply proper_forall_helper.
    auto.
    intros x1 H2.
    apply Vertices.for_all_spec.
    apply annoyingProperV2.
    intros x H1.
    rewrite negb_true_iff.
    apply H with (x := x1) (y := x) in H2; auto.
    rewrite <- Edges.mem_spec in H2.
    apply not_true_is_false in H2.
    auto.
  Qed.

  (* The set contains only those vertices that are in G *)
  Definition ValidSet (X : Vertices.t) (G : t) :=
    forall x, Vertices.In x X -> Vertices.In x (DG.enumVertices G).

  Definition validSet (X : Vertices.t) (G : t) : bool :=
    Vertices.for_all (fun x => if Vertices.mem x X then Vertices.mem x (DG.enumVertices G) else true) X.

  Lemma ProperPifProof : forall X G,  Proper (Vertices.E.eq ==> eq)
     (fun x0 : vertex =>
      if Vertices.mem x0 X
      then Vertices.mem x0 (enumVertices G)
      else true).
  Proof.
    unfold Proper.
    unfold respectful.
    intros.
    destruct (Vertices.mem x X) eqn:H3.
    destruct (Vertices.mem y X) eqn:H4.
    rewrite H.
    auto.
    rewrite <- H in H4.
    apply DG_Facts.VertProperties.P.Dec.F.not_mem_iff in H4.
    apply Vertices.mem_spec in H3.
    apply H4 in H3.
    destruct H3.
    rewrite <- H.
    rewrite H3.
    auto.
  Qed.


  Theorem validSet_true_iff : forall X G, reflect (ValidSet X G)( validSet X G).
  Proof.
    intros.
    apply iff_reflect.
    symmetry.
    unfold validSet, ValidSet.
    split; intros; auto.
    {
      apply Vertices.mem_spec.
      apply Vertices.for_all_spec in H.
      unfold Vertices.For_all in H.
      assert( Vertices.In x X) by auto.
      apply H in H0.
      apply Vertices.mem_spec in H1.
      rewrite H1 in H0.
      auto.
      {
        apply ProperPifProof.
      }
    }
    apply Vertices.for_all_spec.
    {
      apply ProperPifProof.
    }
    intros x H1.
    assert (Vertices.In x X) by auto.
    apply H in H0.
    rewrite <- Vertices.mem_spec in H1,H0.
    rewrite H1; auto.
  Qed.
  
  Theorem validSetRecr : 
    forall x (X : Vertices.t) G,
      ValidSet (Vertices.add x X) G -> ValidSet X G.
  Proof.
    unfold ValidSet. intros. 
    apply H.
    apply Vertices.add_spec.
    auto.
  Qed.

  (* An IndSet is an independent set that is valid *)
  Inductive IndSet (X : Vertices.t) (G : t) :=
  | defIndSet : ValidSet X G -> IndependentSet X G -> IndSet X G. 

  Definition indSet (X : Vertices.t) (G : t) : bool :=
    validSet X G && independentSet X G.

  Theorem indSet_reflect : forall X G, reflect (IndSet X G) (indSet X G).
  Proof.
    intros.
    apply  iff_reflect.
    unfold indSet.
    assert (reflect (ValidSet X G) (validSet X G)).
    apply validSet_true_iff.
    split; try constructor; intuition.
    destruct (independentSet_true_iff X G);
      destruct (validSet_true_iff X G); auto;
    inversion H0;
    contradiction.
    apply andb_true_iff in H0.
    destruct H0.
    destruct (validSet_true_iff X G); auto.
    inversion H0.
    destruct (independentSet_true_iff X G); auto.
    apply andb_true_iff in H0.
    destruct H0. inversion H1.
  Qed.

  Theorem nilIndSet : IndSet Vertices.empty DG.empty.
  Proof.
    constructor;
      try constructor; try intros x y H; unfold ValidSet; intros;
      try apply vert_prop.Dec.F.empty_iff in H;
      try contradiction.    
  Qed.

  Theorem empty_IndSet_spec : forall G, IndSet Vertices.empty G.
  Proof.
    intros.
    constructor.
    unfold ValidSet.
    intros.
    apply vert_prop.Dec.F.empty_iff in H.
    destruct H.
    unfold IndependentSet.
    intros.
    apply vert_prop.Dec.F.empty_iff in H.
    destruct H.
  Qed.
  
  Theorem nilIndSetAdd : forall x G, Vertices.In x (enumVertices G) ->
                       IndSet (Vertices.add x Vertices.empty) G.
  Proof.
    intros x G H.
    constructor.
    unfold ValidSet.
    intros.
    apply Vertices.add_spec in H0.
    destruct H0.
    rewrite H0.
    auto.
    apply vert_prop.Dec.F.empty_iff in H0; contradiction.
    unfold IndependentSet.
    intros.
    intros Hnot.
    rewrite Vertices.add_spec in H0,H1.
    destruct H0.
    destruct H1.
    rewrite H0 in Hnot.
    rewrite H1 in Hnot.
    apply IsEdgeEnum in Hnot.
    apply edges_irreflexive in Hnot.
    auto.
    apply vert_prop.Dec.F.empty_iff in H1; contradiction.
    apply vert_prop.Dec.F.empty_iff in H0; contradiction.
  Qed.

  Import DG_Facts.
  Add Morphism IndSet
      with signature Vertices.eq ==> EqualGraph ==> iff
        as indSet_morph.
  Proof.
    split; intros; constructor; inversion H1; 
      unfold ValidSet, IndependentSet in *; intros.
    {
      intros.
      rewrite  <- H0.
      apply H2.
      rewrite H.
      auto.
    }
    {
      intros.
      rewrite <- H0.
      apply H3; 
        rewrite H; auto.
    }
    {
      rewrite  H0.
      apply H2.
      rewrite <- H.
      auto.
    }
    {
      intros.
      rewrite  H0.
      apply H3; rewrite <- H; auto.
    }
    Qed.

  Lemma IndSet_add  : forall x X G, IndSet (Vertices.add x X) G -> IndSet X G.
    Proof.
      intros.
      constructor;
      inversion H.
      unfold ValidSet in *.
      intros.
      apply H0.
      apply Vertices.add_spec.
      intuition.
      unfold IndependentSet in *.
      intros.
      apply H1;
      apply Vertices.add_spec; intuition.
    Qed.

  End independentSets.



