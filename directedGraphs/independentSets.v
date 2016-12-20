Require Import MSets MSetRBT.
Require Import  SimpleUndirectedGraphs DirectedGraphs_morph.
Require Import PArith.



Module independentSets (DG : SimpleUndirectedGraphs).
  Import DG.
  Module DG_Facts := DirectedGraphMorph DG.


  Add Morphism DG.enumEdges 
      with signature DG_Facts.EqualGraph ==> Edges.eq 
        as IsVertex_morph.
  Proof.
    intros.
    destruct H.
    rewrite H0.
    constructor; auto.
  Qed.

  Add Morphism DG.buildEdge
  with signature Vertices.E.eq ==> Vertices.E.eq ==> Edges.E.eq
    as buildEdge_morph.
  Proof.
    Admitted.


  Module vert_prop := WProperties (DG.Vertices).
  Module Import vertFacts := OrderedTypeFacts Vertices.E.
  Open Scope  positive_scope.
  
  Definition IndependentSet (X : Vertices.t) (G : t) :=
    forall x y, Vertices.In x X -> Vertices.In y X ->
                ~ Edges.In (buildEdge x y) (DG.enumEdges G).

  Definition independentSet (X : Vertices.t) (G : t) :=
    Vertices.for_all (fun v1 => Vertices.for_all
    (fun v2 => negb (Edges.mem (buildEdge v1 v2) (enumEdges G))) X) X.

  Theorem independentSet_true_iff :
    forall X G,
  independentSet X G = true <-> IndependentSet X G. 
  Proof.
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
    unfold Proper.
    unfold respectful.
    intros.
    rewrite H3.
    admit.
    admit.
    apply Vertices.for_all_spec.
    admit.
    intros x H1.
    apply Vertices.for_all_spec.
    admit.
    intros x1 H2.
    apply H with (x := x) (y := x1) in H1; auto.
    rewrite <- Edges.mem_spec in H1.
    apply negb_true_iff.
    apply not_true_is_false in H1.
    auto.
  Admitted.

  Definition ValidSet (X : Vertices.t) (G : DG.t) :=
    forall x, Vertices.In x X -> Vertices.In x (DG.enumVertices G).

  Definition validSet (X : Vertices.t) (G : DG.t) : bool :=
    Vertices.for_all (fun x => if Vertices.mem x X then Vertices.mem x (DG.enumVertices G) else true) X.

  Theorem validSet_true_iff : forall X G, validSet X G = true <-> ValidSet X G.
  Proof.
    unfold validSet, ValidSet.
    split; intros; auto.
    apply Vertices.mem_spec.
    apply Vertices.for_all_spec in H.
    unfold Vertices.For_all in H.
    assert( Vertices.In x X) by auto.
    apply H in H0.
    apply Vertices.mem_spec in H1.
    rewrite H1 in H0.
    auto.
    admit.
    apply Vertices.for_all_spec.
    admit.
    intros x H1.
    assert (Vertices.In x X) by auto.
    apply H in H0.
    rewrite <- Vertices.mem_spec in H1,H0.
    rewrite H1; auto.
  Admitted.
  
  Inductive IndSet (X : Vertices.t) (G : DG.t) :=
  | defIndSet : ValidSet X G -> IndependentSet X G -> IndSet X G. 

  Definition indSet (X : Vertices.t) (G : DG.t) : bool :=
    validSet X G && independentSet X G.

  Theorem indSet_true_iff : forall X G, indSet X G = true <-> IndSet X G.
  Proof.
    intros.
    unfold indSet.
    split; try constructor;
      try apply andb_true_iff in H;
      try rewrite validSet_true_iff in H;
      try rewrite independentSet_true_iff in H;
      intuition.
    inversion H.
   rewrite andb_true_iff.
   rewrite validSet_true_iff;
   rewrite independentSet_true_iff; intuition.
  Qed.


  Inductive MaximalIndSet (X : Vertices.t) (G : DG.t) : Prop :=
  | defMaximalIndSet :
      IndSet X G ->
      (forall x, IndSet (Vertices.add x X) G -> Vertices.In x X) ->
      MaximalIndSet X G.

  Inductive MaximalIndSet_contrapos
  (X : Vertices.t) (G : DG.t) : Prop :=
  | defMaximalIndSet_contrapos :
      IndSet X G ->
      (forall x, ~ Vertices.In x X -> ~ IndSet (Vertices.add x X) G) ->
      MaximalIndSet_contrapos X G.

  Theorem MaximalIndSet_eq : forall X G, MaximalIndSet X G <-> MaximalIndSet_contrapos X G.
  Proof.
    split; intros H; constructor; inversion H; try intros x; auto.
    destruct (vert_prop.In_dec x) with (s := X); auto.
    apply H1 in n.
    contradiction.
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

  Definition MkMaximalIndSet (X : Vertices.t) (G : DG.t) : Vertices.t :=
    Vertices.fold (fun x X' =>
                     if indSet (Vertices.add x X') G &&
                               negb (Vertices.mem x X')  then
                       (Vertices.add x X') else X') (enumVertices G) X.
  
  Theorem MkMaximalIndSet_spec : forall X G,
      IndSet X G -> IndSet (MkMaximalIndSet X G) G.
  Proof.
    intros X G H.
    unfold MkMaximalIndSet.
    apply DG_Facts.VertProperties.P.fold_rec_weak; intros; auto.
        destruct (indSet (Vertices.add x a) G) eqn:H4;
      try apply indSet_true_iff in H4;
      auto.
    destruct (negb (Vertices.mem x a)); auto.
  Qed.

  Theorem nilIndSet : IndSet Vertices.empty DG.empty.
  Proof.
    constructor;
      try constructor; try intros x y H; unfold ValidSet; intros;
      try apply vert_prop.Dec.F.empty_iff in H;
      try contradiction.    
  Qed.


  Theorem TrivialIndSet : MaximalIndSet Vertices.empty DG.empty.
  Proof.
    Admitted.

  Lemma MaximalIndSet_spec : forall X G x,
      MaximalIndSet X G -> ~IndSet (Vertices.add x X) G.
  Proof.
    unfold not.
    intros.
    inversion H.
    assert (IndSet (Vertices.add x X) G) by auto.
    apply H2 in H3.
    apply indSet_true_iff in H0.
    unfold indSet in H0.
    

    inversion H0.
    


  Theorem MkMaximalIndSet_spec2 : forall X G,
      IndSet X G-> MaximalIndSet (MkMaximalIndSet X G) G.
  Proof.
    intros.
    constructor.
    apply MkMaximalIndSet_spec; auto.
    intros.
    assert (IndSet (Vertices.add x (MkMaximalIndSet X G)) G) by auto.
    assert (~IndSet (Vertices.add x (MkMaximalIndSet X G)) G).
    apply MaximalIndSet_spec.
    constructor.
    apply MkMaximalIndSet_spec.
    auto.
    intros.
    

    contradiction.


    constructor. auto.
    intros.
    

destruct H0.
    

    intros.
    unfold MkMaximalIndSet.
    apply indSet_true_iff in H0.
    
    unfold indSet in H0.
    apply DG_Facts.VertProperties.P.fold_rec_weak; intros; auto.
    


    Focus 2.
    destruct (indSet (Vertices.add x0 a) G); auto.
    apply Vertices.add_spec.
    auto.
    unfold MkMaximalIndSet in H0.


    inversion H0.


    




