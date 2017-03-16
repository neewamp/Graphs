Require Export MSetInterface.

Module SetOrd (Vertices : Sets).

  Definition le (s s' : Vertices.t) : Prop := Vertices.Equal s s' \/ Vertices.lt s s'.

  Lemma pre_le : PreOrder le.
  Proof.
    intros.
    constructor.
    unfold le.
    left.
    reflexivity.
    unfold le.
    unfold Transitive.    
    intros.
    destruct H; destruct H0; auto.
    left. rewrite H. auto.
    right. rewrite H. auto.
    right. rewrite  <- H0. auto.
    right. rewrite H. auto.
  Qed.

  Lemma PartialOrder_le : forall (preo : PreOrder le), PartialOrder Vertices.Equal le .
  Proof.
    intros.
    constructor.
    intros.
    constructor.
    left.
    auto.
    left.
    symmetry.
    auto.
    intros.
    inversion H.
    unfold le in H0,H1.
    destruct H0,H1;
    auto; try symmetry; auto.
    assert ((StrictOrder Vertices.lt)).
    apply Vertices.lt_strorder.
    apply StrictOrder_Asymmetric in H2.
    exfalso.
    apply (H2 x x0 H0 H1).
  Qed.

  Lemma compare_le_spec : forall s s' : Vertices.t,
CompSpec Vertices.eq le s s' (Vertices.compare s s').
  Proof.
    intros.
      destruct (Vertices.compare_spec s s'); unfold le; try contradiction; auto.
  Qed.

(* Make sure that things are sorted eventually *)
  Inductive le_list : list Vertices.E.t -> list Vertices.E.t -> Prop :=
  | le_nil : forall (s : list Vertices.E.t),
     le_list nil s
  | le_cons_lt : forall (x y : Vertices.E.t) (s s' : list Vertices.E.t),
      Vertices.E.lt x y ->
      le_list (x :: s) (y :: s')
  | le_cons_eq : forall (x y : Vertices.E.t) (s s' : list Vertices.E.t),
      Vertices.E.eq x  y ->
      le_list s s' ->
      le_list (x :: s) (y :: s').

  Module ord := MakeListOrdering Vertices.E.
  
  (* Lemma le_list_dec : forall l l', ~ eqlistA  Vertices.E.eq l l' -> {le_list l l'} + {le_list l' l}. *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)
  
  Hint Constructors le_list.
  (* Definition lt := le_list. *)

  Lemma lt_preorder : PreOrder le_list.
  Proof.
    split.
    {
      unfold Reflexive.
      intros.
      induction x;
      auto.       
      constructor 3; auto.
      reflexivity. 
    }
    intros s s' s'' H; generalize s''; clear s''; elim H; auto.
      intros.
      inversion_clear H1; auto.
      constructor 2.
      transitivity y; auto.
      constructor 2.  rewrite <- H2; auto.
      intros.
      inversion_clear H3.
      constructor 2. rewrite H0; auto.
      constructor 3; auto. transitivity y; auto.
  Qed.

  

  Definition le_set s s' : Prop :=
    le_list (Vertices.elements s)  (Vertices.elements s').
  Hint Unfold le_set.
  Require Import MSets.
  Module ordV := OrdProperties Vertices.

  Open Scope nat_scope.
Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; try reflexivity; auto;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac si :=
  try contradiction; solve_by_inverts 2.


  Theorem elementsList_eq : forall s1 s2,
      Vertices.eq s1 s2 -> eqlistA Vertices.E.eq (Vertices.elements s1) (Vertices.elements s2).
  Proof.
    intros.
    induction s1 using ordV.set_induction_max.
    induction s2 using ordV.set_induction_max.
    rewrite  ordV.P.elements_Empty in H0,H1.
    rewrite  H0,H1.
    +      constructor.
    +
      assert (ordV.P.Add x s2_1 s2_2) by auto.
      rewrite  ordV.P.Add_Equal in H2.
      symmetry.
      rewrite  ordV.elements_Add_Above with (s := s2_1) (x := x);                   auto.
      symmetry.
      apply  ordV.elements_Add_Above; auto.
      rewrite  ordV.P.Add_Equal.
      rewrite H.
      auto.
    +
      assert (ordV.P.Add x s1_1 s1_2) by auto.
      rewrite  ordV.P.Add_Equal in H2.
      symmetry.
      rewrite  ordV.elements_Add_Above with (s := s1_1) (x := x);                   auto.
      symmetry.
      apply  ordV.elements_Add_Above; auto.
      rewrite  ordV.P.Add_Equal.
      rewrite <- H.
      auto.
  Qed.
  

  Theorem elementsList_eq_iff : forall s1 s2,
      Vertices.eq s1 s2 <-> eqlistA Vertices.E.eq (Vertices.elements s1) (Vertices.elements s2).
  Proof.
    split;
    intros.
    {
      apply elementsList_eq.
      auto.
    }
    {
      unfold Vertices.eq.
      unfold Vertices.Equal.
      intros a.
      revert H.
      do 2 rewrite <- Vertices.elements_spec1.
      generalize (Vertices.elements s2) as l2.
      generalize (Vertices.elements s1) as l1.
      split; intros.
      +
        inversion H;
          subst; try si.
        inversion H0.
        subst.
        constructor; 
          rewrite H4.
        auto.
        subst.
        rewrite <- H.
        auto.
      +
        inversion H;
          subst; try si.
        inversion H0.
        subst.
        constructor; 
          rewrite H4.
        symmetry. auto.
        subst.
        rewrite H.
        auto.
    }
  Qed.


  Definition my_eqlistA  := eqlistA Vertices.E.eq.
    
  Lemma le_eqlistAOrlt : forall l l', le_list l l' <->
                 eqlistA Vertices.E.eq l l' \/  ord.lt_list l l'.
    Proof.
      split;
      intros.
      induction H.
      destruct s; intuition.
      right.
      constructor. auto.
      destruct IHle_list.
      left.
      constructor; auto.
      right.
      constructor 3;
      auto.
      +
        destruct H.
        induction H.
        constructor.
        subst.
        constructor 3;
          auto.
        induction H.
        subst.
        constructor.
        subst.
        constructor 2; auto.
        constructor 3; subst; auto.
    Qed.

  Add Morphism le_list
        with signature my_eqlistA ==> my_eqlistA ==> iff
          as le_list_morph.
    Proof.
      split; intros;
      unfold le_set in *; auto;
      unfold my_eqlistA in *;
      apply le_eqlistAOrlt;
      apply le_eqlistAOrlt in H1.
      +      
        destruct H1;
          [left | right];
          rewrite <- H;
          rewrite <-H0;
          auto.
      +
        destruct H1;
          [left | right];
          rewrite H;
          rewrite H0;
          auto.
    Qed.

  Add Morphism le_set
      with signature Vertices.eq ==> Vertices.eq ==> iff
        as le_set_morph.
  Proof.
    intros.
    unfold le_set.
    apply elementsList_eq in H.
    apply elementsList_eq in H0.
    rewrite H0,H.
    split; auto.
  Qed.

  Lemma Vert_eq_refl : forall x, Vertices.E.eq x x.
    Proof.
      reflexivity.
    Qed.

  Hint Resolve Vert_eq_refl.
  
  Lemma le_list_refl : forall x, le_list x x.
    Proof.
      intros.
      induction x; auto.
    Qed.

   Hint Resolve le_list_refl.
   Hint Unfold flip.

  Lemma le_PartialOrder : forall (preo : PreOrder le_set), PartialOrder Vertices.Equal le_set.
  Proof.
    intros.
    constructor.
    intros.
    constructor; [rewrite <- H| rewrite H]; auto.
    intros.
    inversion H.
    unfold flip in H1.
    unfold le_set in H0,H1.
    rewrite le_eqlistAOrlt in H1,H0.
    destruct H0,H1;
    apply elementsList_eq_iff;
    auto.
    symmetry.
    auto.
    assert (StrictOrder ord.lt_list).
    apply ord.lt_strorder.
    apply StrictOrder_Asymmetric in H2.
    exfalso.
    unfold Asymmetric in H2.
    eapply H2; eauto.
  Qed.
    
End SetOrd.