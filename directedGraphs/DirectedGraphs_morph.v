(* This file implements a number of (endo?)morphisms? *)
Require Import DirectedGraphs.
Require Import Setoid.
(* Need to make sure this doesn't pollute the definitions in bool_scope *)
Require Import Bool.
Open Scope bool.

Module Type DirectedGraphMorph.
  Declare Module Import DG : DirectedGraphs.

  Section Equality.
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
  End Equality.

  Section Rewriting.
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
        case (Edges.E.eq_dec e e1); intros H2.
        {
          rewrite H2.
          do 2 rewrite <- IsEdgeEnum;
          split; intros H3.
          replace e2 with e1.
          erewrite with IsEdges_morph H3.
          admit. admit.
        }
        admit.
      }
    Admitted.
  

End DirectedGraphFacts.
