Require Import GraphInterface
        MathClasses.interfaces.finite_sets
        MathClasses.theory.finite_sets.
Require Import MathClasses.implementations.list_finite_set
        MathClasses.orders.lattices
        MathClasses.orders.orders.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import Bool.
(*         MathClasses.interfaces.orders. *)
Set Implicit Arguments.

Ltac solve_by_inverts n :=
  try red;
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; try reflexivity; eauto;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac si :=
  (intros; try setoid_discriminate; eauto; 
  try match goal with
      | H : _ /\ _ |- _ => intuition
      | |- _ /\ _ => intuition
      end;
  intros; eauto;
  try solve_by_inverts 4); eauto.

Section IndependentSets.
  Context `(SG : SimpleUndirectedGraph).
  Definition asdf : Type.
    
  Program  Definition IndependentSet (X : set_type vertex) (g : t) :=
    forall (x y : vertex),
      contains x X -> contains y X ->
      ~contains (buildEdge x y) (enumEdges g).

  (* Context `(listset vertex). *)
  (* Definition asdf : Type. *)
  
  Definition independentSet (X : set_type vertex) (G : t)
    := for_all (fun v1 => for_all
        (fun v2 => negb (mem (buildEdge v1 v2) (enumEdges G))) X) X.
  

  Theorem independentSet_true_iff :
    forall X G,
  reflect (IndependentSet X G) (independentSet X G). 
  Proof.
    intros.
    apply iff_reflect.
    symmetry.
    unfold independentSet, IndependentSet.
    split; intros.
    {
      intros Hnot.
      rewrite for_all_forall in H.
      apply H in H0.
      rewrite for_all_forall in H0.
      apply H0 in H1.
      rewrite negb_true_iff in H1.
      destruct (mem_reflect (buildEdge x y) (enumEdges G)); 
      si.
    }
    repeat (rewrite for_all_forall; intros).
    rewrite negb_true_iff.
    destruct (mem_reflect (buildEdge v v0) (enumEdges G)); auto.
    exfalso.
    apply (H v v0); auto.
  Qed.

  Definition ValidSet (X : set_type vertex) (G : t) :=
    forall (x : vertex) , contains x X -> contains x (enumVertices G).

  Definition validSet (X : set_type vertex) (G : t) : bool :=
    for_all (fun  x => if mem x X then mem x (enumVertices G) 
            else true ) X.

  Theorem validSet_true_iff :
    forall X G, reflect (ValidSet X G) (validSet X G).
  Proof.
    intros.
    apply iff_reflect.
    symmetry.
    unfold validSet, ValidSet.
    rewrite for_all_forall.
    split; intros; auto.
    {
      assert (x ∈ X) by auto.
      rewrite mem_iff in H0; auto.
      apply H in H1.
      rewrite mem_iff; auto.
      rewrite H0 in H1; auto.
    }
    assert (contains v X) by auto.
    apply H in H0.
    rewrite mem_iff in H0,H1; auto.
    rewrite H1; auto.
  Qed.

  Theorem validSetRecr : 
    forall x (X : set_type vertex) G,
      ValidSet (join x X) G -> ValidSet X G.
  Proof.
    red. intros.
    unfold ValidSet in *.
    apply H; auto.
    rewrite fset_in_join.
    auto.
  Qed.


  Inductive IndSet (X : set_type vertex) (G : t) :=
  | defIndSet : ValidSet X G -> IndependentSet X G -> IndSet X G. 

  Definition indSet (X : set_type vertex) (G : t) : bool :=
    validSet X G && independentSet X G.

  Theorem indSet_reflect : forall X G, reflect (IndSet X G) (indSet X G).
  Proof.
    intros.
    apply iff_reflect.
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
    destruct (validSet_true_iff X G); auto;
    si.
    destruct (independentSet_true_iff X G); auto.
    apply andb_true_iff in H0.
    si.
  Qed.

  Theorem nilIndSet : IndSet bottom empty.
  Proof.
     constructor; unfold IndependentSet;
      try constructor; try intros x y H; unfold ValidSet; intros;
      try apply fset_notin_empty in H; 
      try contradiction.    
  Qed.

  Theorem empty_IndSet_spec : forall G, IndSet bottom G.
  Proof.
    intros.
    constructor.
    unfold ValidSet.
    intros.
    apply fset_notin_empty in H.
    contradiction.
    unfold IndependentSet.
    intros.
    apply fset_notin_empty in H.
    contradiction.
  Qed.

  Theorem nilIndSetAdd : forall x G, contains x (enumVertices G) ->
                       IndSet (join {{x}} bottom) G.
  Proof.
    intros x G H12.
    constructor.
    {
      unfold ValidSet.
      intros.
      rewrite fset_in_add in H.
      destruct H.
      rewrite H;
        auto.
      apply fset_notin_empty in H; contradiction.
    }      
    unfold IndependentSet.
    intros.
    intros Hnot.
    rewrite fset_in_add in H,H0.
    destruct H.
    destruct H0.
    subst.
    admit.
    (* eapply IsEdgeEnum  in Hnot; eauto. *)
    (* rewrite H9 in Hnot. *)
    (* apply edges_irreflexive in Hnot. *)
    apply fset_notin_empty in H0; contradiction.
    apply fset_notin_empty in H; contradiction.
  Admitted.




