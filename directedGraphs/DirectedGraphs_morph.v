(* This file implements a number of (endo?)morphisms? *)
Require Import DirectedGraphs.
Require Import Setoid Bool MSetProperties.
(* Need to make sure this doesn't pollute the definitions in bool_scope *)

Open Scope bool.


Module DirectedGraphMorph (DG : DirectedGraphs).
  (* Declare Module Import DG : DirectedGraphs. *)
  Import DG.

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

    (* Consider deleting *)
    Add Morphism (fun e g => IsEdge e g /\
                             IsVertex (fst (destructEdge e)) g)
      with signature Edges.E.eq ==> EqualGraph ==> iff
    as EdgeDest1.
    Proof.
      intros e1 e2 H0 G1 G2 H1.
      split; intros [H2 H3]; split.
      + rewrite <- H0, <- H1. auto.
      + rewrite H0, H1 in H2. apply Edge_exists1 in H2; auto.
      + rewrite <- H0, <- H1 in H2. auto.
      + rewrite <- H0, <- H1 in H2. apply Edge_exists1 in H2; auto.
    Qed.

    Add Morphism (fun e g => IsEdge e g /\
                             IsVertex (snd (destructEdge e)) g)
      with signature Edges.E.eq ==> EqualGraph ==> iff
    as EdgeDest2.
    Proof.
      intros e1 e2 H0 G1 G2 H1.
      split; intros [H2 H3]; split.
      + rewrite <- H0, <- H1. auto.
      + rewrite H0, H1 in H2. apply Edge_exists2 in H2; auto.
      + rewrite <- H0, <- H1 in H2. auto.
      + rewrite <- H0, <- H1 in H2. apply Edge_exists2 in H2; auto.
    Qed.

  Module Import VertProperties := OrdProperties Vertices.
  Module Import EdgeProperties := OrdProperties Edges.

Inductive GraphConst1 : t -> Type :=
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

  Lemma addEdge_pres :
    forall e1 e2 G, IsEdge e1 G ->
      IsEdge e1 (addEdge e2 G).
  Proof.
    intros e1 e2 G H0.
    case (Edges.E.eq_dec e1 e2); intros H2.
    rewrite H2. apply addEdge_spec1.
    apply Edge_exists1. rewrite <- H2; auto.
    apply Edge_exists2. rewrite <- H2; auto.
    apply addEdge_spec2; auto.
  Qed.

  Lemma transposeAddVertex :
    transpose EqualGraph (fun (v0 : Vertices.elt) (G0 : t) => addVertex v0 G0).
  Proof.
    intros v1 v2 G. constructor.
    + intros v. do 2 rewrite <- IsVertexEnum.
      split; intros.
      case (Vertices.E.eq_dec v v2); intros.
        rewrite e. apply addVertex_spec1.
        apply addVertex_spec2; auto.
          case (Vertices.E.eq_dec v v1); intros.
          rewrite e. apply addVertex_spec1.
          apply addVertex_spec2; auto.
          do 2 apply addVertex_spec2 in H; auto.
      case (Vertices.E.eq_dec v v1); intros.
        rewrite e. apply addVertex_spec1.
        apply addVertex_spec2; auto.
          case (Vertices.E.eq_dec v v2); intros.
          rewrite e. apply addVertex_spec1.
          apply addVertex_spec2; auto.
          do 2 apply addVertex_spec2 in H; auto.
    + intros e. do 2 rewrite <- IsEdgeEnum. split; intros;
      do 2 apply addVertex_spec3 in H; do 2 apply addVertex_spec3; auto.
  Qed.

  Lemma transposeAddEdge :
    transpose EqualGraph (fun (e0 : Edges.elt) (G0 : t) => addEdge e0 G0).
  Proof.
    split. unfold Vertices.eq.
    + split; intros; try rewrite <- IsVertexEnum in *;
      try do 2 rewrite <- addEdge_spec3 in *; auto.
    + split; intros; rewrite <- IsEdgeEnum in *.
      case (Edges.E.eq_dec a y); intros.
      rewrite e in H |-*.
      - assert (IsVertex (fst (destructEdge y)) z) as H0.
          apply Edge_exists1 in H; do 2 rewrite <- addEdge_spec3 in H; auto.
        assert (IsVertex (snd (destructEdge y)) z) as H1.
          apply Edge_exists2 in H; do 2 rewrite <- addEdge_spec3 in H; auto.
        apply addEdge_spec1; apply addEdge_spec3; auto.
      - apply addEdge_spec2; auto. case (Edges.E.eq_dec a x); intros.
        rewrite e in H |-*.  apply addEdge_spec1;
        [apply Edge_exists1 in H | apply Edge_exists2 in H];
        do 2 apply addEdge_spec3 in H; auto. do 2 apply addEdge_spec2 in H; auto.
        apply addEdge_spec2; auto.
      - case (Edges.E.eq_dec a x); intros.
        rewrite e in H |-*.
        * assert (IsVertex (fst (destructEdge x)) z) as H0.
            apply Edge_exists1 in H; do 2 rewrite <- addEdge_spec3 in H; auto.
          assert (IsVertex (snd (destructEdge x)) z) as H1.
            apply Edge_exists2 in H; do 2 rewrite <- addEdge_spec3 in H; auto.
          apply addEdge_spec1; auto; apply addEdge_spec3; auto.
        * apply addEdge_spec2; auto. case (Edges.E.eq_dec a y); intros.
        rewrite e in H |-*.  apply addEdge_spec1;
        [apply Edge_exists1 in H | apply Edge_exists2 in H];
        do 2 apply addEdge_spec3 in H; auto. do 2 apply addEdge_spec2 in H; auto.
        apply addEdge_spec2; auto.
  Qed.

  Lemma addEdges_pres :
    forall e E G, IsEdge e G ->
      IsEdge e (addEdges E G).
  Proof.
    intros. unfold addEdges. apply EdgeProperties.P.fold_rec_weak;
    try solve [auto | split; auto].
    intros e1 g V H0 H1. apply addEdge_pres; auto.
  Qed.

  Lemma addEdges_spec2 :
    forall v E G, IsVertex v (addEdges E G) <-> IsVertex v G.
  Proof.
    intros v E G. unfold addEdges. apply P.fold_rec_weak.
    auto. split; auto.
    intros. rewrite <- H0. symmetry. apply addEdge_spec3.
  Qed.
(*
  Lemma addEdges_morph_aux1 :
    forall E1 E2 G, E1 =E= E2 -> addEdges E1 G =G= addEdges E2 G.
  Proof.
    intros. split.
    + intros v; split; intros H0; rewrite <- IsVertexEnum in *;
      apply addEdges_spec2 in H0; apply addEdges_spec2; auto.
    + intros e; split; intros H0; rewrite <- IsEdgeEnum in *;
      unfold addEdges in *. admit. admit.
  Admitted.
*)
  Lemma addEdges_morph_aux2 :
    forall E G1 G2, G1 =G= G2 -> addEdges E G1 =G= addEdges E G2.
  Proof.
    intros. split.
    + intros v; split; intros H0; rewrite <- IsVertexEnum in *;
      apply addEdges_spec2 in H0; apply addEdges_spec2;
      [rewrite <- H | rewrite H]; auto.
    + unfold addEdges. intros v. do 2 rewrite <- IsEdgeEnum. 
      induction E using P.set_induction.
      - split; intros; rewrite P.fold_1b in *; auto;
        [rewrite <- H | rewrite H]; auto.
      - intros. rewrite (@P.fold_2 E1 E2 x); auto. rewrite (@P.fold_2 E1 E2 x); auto.
        case (Edges.E.eq_dec v x); intros.
        * rewrite e. split; intros; apply addEdge_spec1; apply addEdges_spec2;
          [apply Edge_exists1 in H2 | apply Edge_exists2 in H2 |
           apply Edge_exists1 in H2 | apply Edge_exists2 in H2];
          apply addEdge_spec3 in H2; apply addEdges_spec2 in H2;
          [rewrite <- H | rewrite <- H | rewrite H | rewrite H]; auto.
        * split; intros H2; apply addEdge_spec2; auto;
          apply addEdge_spec2 in H2; auto; apply IHE1; auto.
        * apply EqualGraph_equiv.
        * intros e1 e2 H2 Ga Gb H3. rewrite H3, H2. apply EqualGraph_equiv.
        * apply transposeAddEdge.
        * apply EqualGraph_equiv.
        * intros e1 e2 H2 Ga Gb H3. rewrite H3, H2. apply EqualGraph_equiv.
        * apply transposeAddEdge.
  Qed.

  Add Morphism addEdges
      with signature Edges.eq ==> EqualGraph ==> EqualGraph
  as addEdges_morph.
  Proof.
    intros. assert (addEdges y x0 =G= addEdges x x0) as H1.
    unfold addEdges. apply P.fold_equal. apply EqualGraph_equiv.
    intros e1 e2 H1 g1 g2 H2. rewrite H2, H1. apply EqualGraph_equiv.
    apply transposeAddEdge. symmetry. apply H. rewrite <- H1.
    apply addEdges_morph_aux2. auto.
  Qed.

 (* Is there a term for possessing the added elements? *)
  Lemma addVertices_spec1 :
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

  Lemma addVertices_spec2 :
    forall e V G, IsEdge e (addVertices V G) <-> IsEdge e G.
  Proof.
    intros e V G.
    unfold addVertices.
    apply VertProperties.P.fold_rec_weak; try solve [auto | split; auto].
    intros s s' G1 H0 H1; auto. rewrite <- H1.
    rewrite <- addVertex_spec3; split; auto.
  Qed.

 
  Lemma addEdges_spec1 :
    forall E e G, (IsVertex (fst (destructEdge e)) G) ->
                (IsVertex (snd (destructEdge e)) G) ->
                Edges.In e E -> IsEdge e (addEdges E G).
  Proof.
    intros E. induction E using P.set_induction_bis.
    + intros. rewrite <- H in H2. specialize (IHE1 e G H0 H1 H2).
      assert (addEdges E1 G =G= addEdges E2 G) as H3. rewrite H.
      reflexivity. rewrite <- H. auto.
    + intros. apply Edges.empty_spec in H1. contradiction.
    + intros. unfold addEdges. rewrite P.fold_add.
      apply Edges.add_spec in H2. case H2; intros.
      - rewrite <- H3. apply addEdge_spec1; apply addEdges_spec2; auto.
      - apply (IHE _ _ H0 H1) in H3. apply addEdge_pres. auto.
      - apply EqualGraph_equiv.
      - unfold respectful. unfold Proper. intros. rewrite H3, H4.
        apply EqualGraph_equiv.
      - apply transposeAddEdge.
      - auto.
  Qed.

  (* Rebuilds the graph according to the graph const *)
  Definition rebuildGraph_GraphConst1 G : t :=
    addEdges (enumEdges G) (addVertices (enumVertices G) empty).

  Lemma addVertices_bleh :
    forall v V, Vertices.In v V -> Vertices.In v (enumVertices (addVertices V empty)).
  Proof.
    intros. rewrite <- IsVertexEnum.
    apply addVertices_spec1; auto.
  Qed.

  Lemma emptyVerts : forall G, IsEmpty G -> forall v, ~ IsVertex v G.
  Proof.
    
  Admitted.

  Lemma emptyEdges : forall G, IsEmpty G -> forall e, ~ IsEdge e G.
  Proof.

  Admitted.    

  Lemma rebuildGraph_GraphConst1_spec1 :
    forall G, (rebuildGraph_GraphConst1 G) =G= G.
  Proof.
    intros G. constructor.
    + unfold rebuildGraph_GraphConst1. intros v.
      do 2 rewrite <- IsVertexEnum. rewrite addEdges_spec2.
      - do 2 rewrite IsVertexEnum.
        induction (enumVertices G) using VertProperties.P.set_induction.
        * unfold addVertices. rewrite VertProperties.P.fold_1b.
          generalize (Empty); intros. apply emptyVerts with (v := v) in H0.
          split; intros. rewrite <- IsVertexEnum in H1. contradiction.
          apply H in H1. contradiction. auto.
        * split; intros.
            unfold addVertices in H1.
            rewrite (@VertProperties.P.fold_2 t0_1 t0_2 x) in H1; auto.
            case (Vertices.E.eq_dec v x); intros H3. rewrite H3. apply H0.
            left. reflexivity. apply H0. right. apply IHt0_1.
            rewrite <- IsVertexEnum in H1. apply addVertex_spec2 in H1; auto.
            rewrite <- IsVertexEnum. apply H1. apply EqualGraph_equiv.
            intros a b H' c d H''. rewrite H', H''. reflexivity.
            apply transposeAddVertex. rewrite <- IsVertexEnum.
            apply addVertices_spec1. auto.
    + unfold rebuildGraph_GraphConst1.
      intros e. do 2 rewrite <- IsEdgeEnum. split.
      - intros. rewrite IsEdgeEnum.
        remember (enumEdges G).
        induction (t0) using EdgeProperties.P.set_induction.
        * unfold addEdges in H. rewrite EdgeProperties.P.fold_1b in H.
          rewrite addVertices_spec2 in H. generalize Empty; intros H1.
          apply emptyEdges with (e := e) in H1. contradiction. auto.
        * apply P.Add_Equal in H1. rewrite H1. unfold addEdges in H.
          admit. (* still needs some work *)
          (* rewrite (@EdgeProperties.P.fold_2 t1_1 t1_2 e) in H; auto.
          admit. apply EqualGraph_equiv.
          intros e1 e2 H' g1 g2 H''. rewrite H', H''. reflexivity.
          apply transposeAddEdge. *)
      - intros H. apply addEdges_spec1;
        try (apply addVertices_spec1; rewrite <- IsVertexEnum).
        apply Edge_exists1; auto. apply Edge_exists2; auto. 
        rewrite <- IsEdgeEnum; auto.
  Admitted.

  Lemma rebuildGraph_GraphConst1_spec2 :
    forall G, GraphConst1 (rebuildGraph_GraphConst1 G).
  Proof.
    intros G. unfold rebuildGraph_GraphConst1, addEdges, addVertices.
    apply EdgeProperties.P.fold_rec_weak;
      try apply VertProperties.P.fold_rec_weak; try constructor; auto.
  Qed.

  Lemma ind1 (P : t -> Prop) (H0 : Respectful Prop P) :
    P empty -> 
    (forall x g, P g -> P (addVertex x g)) ->
    (forall x g, P g -> P (addEdge x g)) ->
      forall g, P g.
  Proof.
    intros.
    unfold Respectful in H0.
    rewrite <- (H0 (rebuildGraph_GraphConst1 g) g).
    induction (rebuildGraph_GraphConst1_spec2 g);
    auto. apply rebuildGraph_GraphConst1_spec1.
  Qed.

  Lemma rec1 (P : t -> Set) ( H0 : Respectful _ P) :
    P empty -> 
    (forall x g, P g -> P (addVertex x g)) ->
    (forall x g, P g -> P (addEdge x g)) ->
      forall g, P g.
  Proof.
    intros.
    unfold Respectful in H0.
    rewrite <- (H0 (rebuildGraph_GraphConst1 g) g).
    induction (rebuildGraph_GraphConst1_spec2 g);
    auto.
    apply rebuildGraph_GraphConst1_spec1.
  Qed.

  Lemma rect1 :
    forall (P : t -> Type) (H0 : Respectful _ P),
      P empty -> 
      (forall x g, P g -> P (addVertex x g)) ->
      (forall x g, P g -> P (addEdge x g)) ->
        forall g, P g.
  Proof.
    intros.
    unfold Respectful in H0.
    rewrite <- (H0 (rebuildGraph_GraphConst1 g) g).
    induction (rebuildGraph_GraphConst1_spec2 g);
    auto.
    apply rebuildGraph_GraphConst1_spec1.
  Qed.

  Definition neighborhood : vertex -> t -> Vertices.t.
  Proof.
    intros. apply rect1.
    constructor. apply Vertices.empty.
    intros. apply X1.
    intros. apply destructEdge in x. destruct x.
    apply (if Vertices.E.eq_dec e X
                then (Vertices.add e0 X1)
                else  X1). exact X0.
  Defined.
    
  Inductive GraphConst2 : t -> Type :=
  | Empty : GraphConst2 empty
  | GrowGraph : forall G,
      GraphConst2 G ->
      forall v1 E,
        (* We require v1 to be a new vertex *)
        ~ IsVertex v1 G ->
        (* All edges in E have v1 as one of their members *)
        (forall e, Edges.In e E -> 
          ((fst (destructEdge e)) =v= v1 \/
          (snd (destructEdge e)) =v= v1)) ->
        (* All edges in E have a vertex of the parent graph as a member *)
        (forall e, Edges.In e E ->
          (IsVertex (fst (destructEdge e)) G \/
           IsVertex (snd (destructEdge e)) G)) ->
       GraphConst2 (addEdges E (addVertex v1 G)).

Module Import vOTF := OrderedTypeFacts Vertices.E.
  (* Generates the edges that need to be added to a graph GN, in order to
      satisfy GraphConst2, with the end goal of reconstructing G, given a vertex v1 *)
  Definition addEdges_GC2 (v1 : vertex) (G : t) (GN : t): Edges.t :=
    Edges.fold
      (fun (e : edge) E =>
            (* Check to see which edges have a source/sink in the graph GN *)
         if ((Vertices.mem (fst (destructEdge e)) (enumVertices GN) ||
             Vertices.mem (snd (destructEdge e)) (enumVertices GN)))
            &&
            (* Ensures that either the source/sink is equal to v1 *)
            (vOTF.eqb v1 (fst (destructEdge e)) ||
            (vOTF.eqb v1 (snd (destructEdge e))))
         then Edges.add e E
         else E)
      (enumEdges G) Edges.empty.

  Definition rebuildGraph_GraphConst2 (G : t) : t :=
    Vertices.fold (fun (v : vertex) (G0 : t) =>
                     addEdges (addEdges_GC2 v G G0) (addVertex v G0))
                  (enumVertices G) empty.
 

    Lemma rebuildGraph_GraphConst2_spec1 :
    forall G, (rebuildGraph_GraphConst2 G) =G= G.
  Proof.
    intros G. constructor.
    {
      constructor; intros H. 
      unfold rebuildGraph_GraphConst2 in H.
      rewrite <- IsVertexEnum. rewrite <- IsVertexEnum in H.
      Admitted.

  Hint Constructors GraphConst2.

  Lemma rebuildGraph_GraphConst2_spec2 :
    forall G, GraphConst2 (rebuildGraph_GraphConst2 G).
  Proof.
    Admitted.
    
  Lemma ind2 (P : t -> Type) (H0 : Respectful _ P) :
    P empty ->
    (forall G, P G ->
      (forall v1 E,
        ~ IsVertex v1 G ->
          (forall e, Edges.In e E -> 
            ((fst (destructEdge e)) =v= v1 \/
            (snd (destructEdge e)) =v= v1)) ->
          (forall e, Edges.In e E ->
            (IsVertex (fst (destructEdge e)) G \/
             IsVertex (snd (destructEdge e)) G)) ->
        P (addEdges E (addVertex v1 G)))) ->
     forall g, P g.
  Proof.
    intros H H1 g.
    rewrite <- (H0 (rebuildGraph_GraphConst2 g) g).
    induction (rebuildGraph_GraphConst2_spec2 g); auto.
    apply rebuildGraph_GraphConst2_spec1.
  Qed.

  Lemma ind3 (P : t -> Type) (H0 : Respectful _ P) :
    (forall G, Vertices.cardinal (enumVertices G) = 0 -> P G) ->
    (forall G n, Vertices.cardinal (enumVertices G) = n ->
      (P G) ->
      (forall G', Vertices.cardinal (enumVertices G') = S n -> P G')) ->
    forall G, P G.
  Proof.
    intros. apply ind2; auto.
    apply X. auto.
    admit.
    intros.
    specialize (X0 G0 (Vertices.cardinal (enumVertices G0))).
    apply X0; auto. admit.
  Admitted.

  Lemma ind4 (P : t -> Type) (H0 : Respectful _ P) :
    (forall G, Vertices.cardinal (enumVertices G) = 0 -> P G) ->
    (forall G G',
      (Vertices.cardinal (enumVertices G) <= Vertices.cardinal (enumVertices G')) ->
      (P G) ->
        (P G')) ->
    forall G, P G.
  Proof.
    intros. apply ind3; auto.
    intros. apply X0 with (G:= G0). rewrite H, H1; auto.
    auto.
  Qed.

End DirectedGraphMorph.