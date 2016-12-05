(* This file implements a number of (endo?)morphisms? *)
Require Import DirectedGraphs.
Require Import Setoid Bool MSetProperties.
(* Need to make sure this doesn't pollute the definitions in bool_scope *)

Open Scope bool.

Module Type DirectedGraphMorph.
  Declare Module Import DG : DirectedGraphs.

    Inductive EqualGraph : t -> t -> Prop :=
    | GraphEQ : forall g1 g2,
                  (enumVertices g1) =V= (enumVertices g2) ->
                  (enumEdges g1) =E= (enumEdges g2) ->
                    EqualGraph g1 g2.

    Definition equalGraph : t -> t -> bool :=
      fun G1 G2 =>
        Vertices.equal (enumVertices G1) (enumVertices G2) &&
        Edges.equal (enumEdges G1) (enumEdges G2).

    Notation "G1 =G= G2" := (EqualGraph G1 G2) (at level 60).

    Definition Respectful (A : Type) (f : t -> A) : Prop :=
      forall G1 G2, G1 =G= G2 -> f G1 = f G2.

    Lemma EqualGraphP G1 G2 : reflect (G1 =G= G2) (equalGraph G1 G2).
    Proof.
      case_eq (equalGraph G1 G2); intros H0;
      unfold equalGraph in H0; constructor;
      [apply andb_true_iff in H0 | apply andb_false_iff in H0; intros H2].
      destruct H0 as [H0 H1]; constructor;
      [apply Vertices.equal_spec | apply Edges.equal_spec]; auto.
      inversion H2. destruct H0 as [H0 | H0];
      [rewrite <- Vertices.equal_spec in H |
       rewrite <- Edges.equal_spec in H1]; congruence.
    Qed.

  (* Lemmas for weakening graph equality *)
    Lemma EqualGraph_weakVertices :
      forall G1 G2, G1 =G= G2 -> (enumVertices G1 =V= enumVertices G2).
    Proof.
      intros G1 G2 H; destruct H as [H0 H1]; auto.
    Qed.


    Lemma EqualGraph_weakEdges :
      forall G1 G2, G1 =G= G2 -> (enumEdges G1 =E= enumEdges G2).
    Proof.
      intros G1 G2 H; destruct H as [H0 H1]; auto.
    Qed.

  (* Relational proofs for easier rewriting *)
    Lemma EqualGraph_equiv : Equivalence EqualGraph.
    Proof.
      do 2 constructor;
      destruct Edges.eq_equiv as [e0 e1 e2];
      destruct Vertices.eq_equiv as [v0 v1 v2]. 
      apply v0. apply e0.
      destruct H as [H H']; apply v1 ; auto.
      destruct H as [H H']; apply e1 ; auto.
      destruct H as [H H']; destruct H0 as [H0 H0']; apply (v2 _ _ _ H1 H3).
      destruct H as [H H']; destruct H0 as [H0 H0']; apply (e2 _ _ _ H2 H4).
    Qed.

    Add Parametric Relation : t EqualGraph
      reflexivity proved by (Equivalence.equiv_reflexive EqualGraph_equiv)
      symmetry proved by (Equivalence.equiv_symmetric EqualGraph_equiv)
      transitivity proved by (Equivalence.equiv_transitive EqualGraph_equiv)
    as eqGraph.

    Add Morphism enumVertices
      with signature EqualGraph ==> Vertices.eq
    as enumVertices_morph.
    Proof.
      intros G1 G2 H0; apply EqualGraph_weakVertices in H0; auto.
    Qed.

    Add Morphism enumEdges
      with signature EqualGraph ==> Edges.eq
    as enumEdges_morph.
    Proof.
      intros G1 G2 H0; apply EqualGraph_weakEdges in H0; auto.
    Qed.

    Add Morphism IsVertex
      with signature Vertices.E.eq ==> EqualGraph ==> iff
    as IsVertex_morph.
    Proof.
      intros v1 v2 H0 G1 G2 H1.
      destruct H1 as [H1 H2].
      do 2 rewrite IsVertexEnum.
      rewrite H0. split; intros H4;
      apply H; auto.
    Qed.

    Add Morphism IsEdge
      with signature Edges.E.eq ==> EqualGraph ==> iff
    as IsEdges_morph.
    Proof.
      intros e1 e2 H0 G1 G2 H1.
      destruct H1 as [H1 H2].
      do 2 rewrite IsEdgeEnum.
      rewrite H0. split; intros H4;
      apply H3; auto.
    Qed.

    Add Morphism addVertex
      with signature Vertices.E.eq ==> EqualGraph ==> EqualGraph
    as addVertex_morph.
    Proof.
      intros v1 v2 H0 G1 G2 H1.
      constructor; intros v.
      {
        case (Vertices.E.eq_dec v v1); intros H2.
        {
          rewrite H2. rewrite H0 at 3.
          do 2 rewrite <- IsVertexEnum;
          split; intros _; apply addVertex_spec1.
        }
        {
          do 2 rewrite <- IsVertexEnum.
          split; intros H3; apply addVertex_spec2;
          apply addVertex_spec2 in H3; auto.
          rewrite <- H0; auto. rewrite <- H1; auto.
          rewrite <- H0; auto. rewrite H1; auto.
          rewrite <- H0; auto.
        }
      }
      {
        do 2 rewrite <- IsEdgeEnum;
        do 2 rewrite <- addVertex_spec3;
        rewrite H1. split; auto.
      }
    Qed.

    Add Morphism addEdge
      with signature Edges.E.eq ==> EqualGraph ==> EqualGraph
    as addEdge_morph.
    Proof.
      intros e1 e2 H0 G1 G2 H1.
      constructor; intros e.
      {
        do 2 rewrite <- IsVertexEnum;
        do 2 rewrite <- addEdge_spec3;
        rewrite H1. split; auto.
      }
      {
        do 2 rewrite <- IsEdgeEnum.
        case (Edges.E.eq_dec e e1); intros H2.
        {
          rewrite H2. split; intros H3;
          [rewrite H0; rewrite H0 in H3 at 1 |];
          apply addEdge_spec1.
          apply Edge_exists1 in H3.
          apply addEdge_spec3 in H3.
          rewrite <- H1; auto.
          apply Edge_exists2 in H3.
          apply addEdge_spec3 in H3.
          rewrite <- H1; auto.
          apply Edge_exists1 in H3.
          apply addEdge_spec3 in H3.
          rewrite H1; auto.
          apply Edge_exists2 in H3.
          apply addEdge_spec3 in H3.
          rewrite H1; auto.
        }
        {
          split; intros H3;
          apply addEdge_spec2 in H3; auto. apply addEdge_spec2.
          rewrite <- H0; auto. rewrite <- H1; auto.
          apply addEdge_spec2; auto. rewrite <- H1 in H3; auto.
          rewrite <- H0; auto.
        }
      }
  Qed.

  Module Import VertProperties := OrdProperties Vertices.
  Module Import EdgeProperties := OrdProperties Edges.

  Section GraphInduction.
  Inductive GraphConst1 : t -> Prop :=
  | EmptyGraph1 : GraphConst1 empty
  | AddVert1 : forall G v, (GraphConst1 G) -> GraphConst1 (addVertex v G)
  | AddEdge1 : forall G e, (GraphConst1 G) -> GraphConst1 (addEdge e G).

(* These definitions could use to be somewhere else *)
  Definition addVertices V G : t :=
    Vertices.fold (fun v g => addVertex v g) V G.

  Definition addEdges E G : t :=
    Edges.fold (fun e G => addEdge e G) E G.

(* Same for these lemmas *)
  Lemma addVertex_pres :
    forall v1 v2 G, IsVertex v1 G ->
      IsVertex v1 (addVertex v2 G).
  Proof.
    intros v1 v2 G H.
    case (Vertices.E.eq_dec v1 v2); intros H2.
    rewrite H2. apply addVertex_spec1.
    apply addVertex_spec2; auto.
  Qed.

  Lemma addVertices_pres :
    forall v V G, IsVertex v G ->
      IsVertex v  (addVertices V G).
  Proof.
    intros v V G H.
    unfold addVertices.
    apply VertProperties.P.fold_rec_weak; try (auto; fail).
    intros x a s s' H0. apply addVertex_pres; auto.
  Qed.

 (* Is there a term for possessing the added elements? *)
  Lemma addVertices_spec :
    forall v V G, Vertices.In v V -> IsVertex v (addVertices V G).
  Proof.
    intros v V G. unfold addVertices. 
    apply VertProperties.P.fold_rec_weak.
    intros s s' H0 H1 H2 H3. rewrite H1 in H2. apply H2; auto.
    intros H. apply Vertices.empty_spec in H; contradiction.
    intros x a s H0 H1 H2. case (Vertices.E.eq_dec v x); intros H3.
    rewrite H3; apply addVertex_spec1.
    apply addVertex_spec2; auto. apply H1. apply Vertices.add_spec in H2.
    case H2; auto. intros H4. apply H3 in H4. contradiction.
  Qed.
    
  (* Rebuilds the graph according to the graph const *)
  Definition rebuildGraph_GraphConst1 G : t :=
    addEdges (enumEdges G) (addVertices (enumVertices G) empty).
  
  Lemma rebuildGraph_GraphConst1_spec1 :
    forall G, (rebuildGraph_GraphConst1 G) =G= G.
  Proof.
    intros G. constructor.
    {
      constructor; intros H.
  Admitted.

  Lemma rebuildGraph_GraphConst1_spec2 :
    forall G, GraphConst1 (rebuildGraph_GraphConst1 G).
  Proof.
    intros G. unfold rebuildGraph_GraphConst1, addEdges, addVertices.
        
  Admitted.

  Print Respectful.
  Lemma ind1 (P : t -> Prop) (H0 : Respectful _ P) :
    P empty -> 
    (forall x g, P g -> P (addVertex x g)) ->
    (forall x g, P g -> P (addEdge x g)) ->
    forall g, P g.
  Admitted.
  
  Lemma rec1 (P : t -> Set) ( H0 : Respectful _ P) :
    P empty -> 
    (forall x g, P g -> P (addVertex x g)) ->
    (forall x g, P g -> P (addEdge x g)) ->
      forall g, P g.
  Admitted.

  Lemma rect1 :
    forall (P : t -> Type) (H0 : Respectful _ P),
      P empty -> 
      (forall x g, P g -> P (addVertex x g)) ->
      (forall x g, P g -> P (addEdge x g)) ->
        forall g, P g.
  Admitted.
  End GraphInduction.
