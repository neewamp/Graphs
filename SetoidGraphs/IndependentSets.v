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
  Context `(Graph).
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
      rewrite for_all_forall in H9.
      apply H9 in H10.
      rewrite for_all_forall in H10.
      apply H10 in H11.
      rewrite negb_true_iff in H11.
      destruct (mem_reflect (buildEdge x y) (enumEdges G)); 
      si.
    }
    repeat (rewrite for_all_forall; intros).
    rewrite negb_true_iff.
    destruct (mem_reflect (buildEdge v v0) (enumEdges G)); auto.
    exfalso.
    apply (H9 v v0); auto.
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
      rewrite mem_iff in H10; auto.
      apply H9 in H11.
      rewrite mem_iff; auto.
      rewrite H10 in H11; auto.
    }
    assert (contains v X) by auto.
    apply H9 in H10.
    rewrite mem_iff in H10,H11; auto.
    rewrite H11; auto.
  Qed.

  Theorem validSetRecr : 
    forall x (X : set_type vertex) G,
      ValidSet (join x X) G -> ValidSet X G.
  Proof.
    red. intros.
    unfold ValidSet in *.
    apply H9; auto.
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
    inversion H10;
    contradiction.
    apply andb_true_iff in H10.
    destruct H10.
    destruct (validSet_true_iff X G); auto;
    si.
    destruct (independentSet_true_iff X G); auto.
    apply andb_true_iff in H10.
    si.
  Qed.


  Theorem nilIndSet : IndSet ⊥ empty.
  Proof.
     constructor; unfold IndependentSet;
      try constructor; try intros x y H; unfold ValidSet; intros;
      try apply fset_notin_empty in H9; 
      try contradiction.    
  Qed.

  Theorem empty_IndSet_spec : forall G, IndSet bottom G.
  Proof.
    intros.
    constructor.
    unfold ValidSet.
    intros.
    apply fset_notin_empty in H9.
    contradiction.
    unfold IndependentSet.
    intros.
    apply fset_notin_empty in H9.
    contradiction.
  Qed.

  Theorem nilIndSetAdd : forall x G, contains x (enumVertices G) ->
                       IndSet (join {{x}} bottom) G.
  Proof.
    intros x G H10.
    constructor.
    {
      unfold ValidSet.
      intros.
      rewrite fset_in_add in H9.
      destruct H9.
      rewrite H9;
        auto.
      apply fset_notin_empty in H9; contradiction.
    }      
    unfold IndependentSet.
    intros.
    intros Hnot.
    rewrite fset_in_add in H9,H11.
    destruct H9.
    destruct H11.
    subst.
    admit.
    (* eapply IsEdgeEnum  in Hnot; eauto. *)
    (* rewrite H9 in Hnot. *)
    (* apply edges_irreflexive in Hnot. *)
    apply fset_notin_empty in H11; contradiction.
    apply fset_notin_empty in H9; contradiction.
  Admitted.




