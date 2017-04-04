Require Export MSetInterface.
Require Import MSets.
Module SetOrd (Vertices : Sets).


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


  Module ordV := OrdProperties Vertices.
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

  Require Import List.

  Module ordVertFacts := OrderedTypeFacts Vertices.E.
  
  Fixpoint le_listb s s' :=
    match s,s' with
    | nil,_ => true
    | (x :: l), nil => false
    | (x::l), (y::l') => if ordVertFacts.lt_dec x y then true
          else if ordVertFacts.eq_dec x y then le_listb l l' else
                           false
    end.

  Lemma le_listReflect : forall l l', reflect (le_list l l')
                                              (le_listb l l').
  Proof.
    intros.
    apply iff_reflect.
    split; intros.
    Focus 2.
    generalize dependent l'.
    induction l;
      induction l'; intros.
    do 2 constructor.
    do 2 constructor.
    inversion H.
    unfold le_listb in H.
    destruct (ordVertFacts.lt_dec a a0) eqn:H1.
    constructor 2.
    auto.
    destruct (ordVertFacts.eq_dec a a0) eqn:H2.
    fold le_listb in H.
    constructor 3.
    auto.
    apply IHl.
    auto.
    inversion H.
    {
      induction H.
      auto.
      unfold le_listb.
      destruct (ordVertFacts.lt_dec x y).
      auto.
      contradiction.
      destruct (ordVertFacts.eq_dec x y ).
      simpl.
      destruct (ordVertFacts.lt_dec x y); auto.
      destruct (ordVertFacts.eq_dec x y ); auto.
      contradiction.
    }
  Qed.

  Module ord := MakeListOrdering Vertices.E.
  
  (* Lemma le_list_dec : forall l l', ~ eqlistA  Vertices.E.eq l l' -> {le_list l l'} + {le_list l' l}. *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)
  
  Hint Constructors le_list.
  (* Definition lt := le_list. *)

  Lemma le_list_refl : Reflexive le_list.
  Proof.
    unfold Reflexive.
    intros.
    induction x;
      auto.
    constructor 3; auto.
    reflexivity.
  Qed.

  Lemma le_list_trans : Transitive le_list.
    Proof.
      unfold Transitive.
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
      
    Theorem le_list_preorder : PreOrder le_list.
    Proof.
      split.
      {
        apply le_list_refl.
      }
      apply le_list_trans.
    Qed.


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
      +
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


  

  Definition le_set s s' : Prop :=
    le_list (Vertices.elements s)  (Vertices.elements s').
  Hint Unfold le_set.

  Definition lt_set s s' :=
    ord.lt_list (Vertices.elements s) (Vertices.elements s').

  Lemma le_set_spec : forall s s', 
  le_set s s' <-> Vertices.eq s s' \/ lt_set s s'.
  Proof.
    intros.
    unfold le_set.
    rewrite elementsList_eq_iff.
    apply le_eqlistAOrlt.
  Qed.

  Definition le_setb s s' : bool :=
    le_listb (Vertices.elements s) (Vertices.elements s').
  
  
  Hint Unfold le_setb.
  Hint Resolve le_listReflect.

  Lemma le_setReflect : forall s s', reflect (le_set s s') (le_setb s s').
  Proof.
    intros.
    unfold le_set.
    unfold le_setb.
    apply le_listReflect.
  Qed.



  Theorem le_setPreOrder : PreOrder le_set.
  Proof.
    unfold le_set.
    constructor.
    unfold Reflexive.
    intros.
    apply le_list_refl.
    unfold Transitive.
    intros.
    eapply le_list_trans; eauto.
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

  Add Morphism lt_set
      with signature Vertices.eq ==> Vertices.eq ==> iff
        as lt_set_morph.
  Proof.
    intros.
    unfold lt_set.
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
  
  Hint Resolve le_list_refl.
  Hint Unfold flip.

  Lemma le_PartialOrder : forall (preo : PreOrder le_set),
      PartialOrder Vertices.Equal le_set.
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
  
  Lemma helper : forall t x a y ,~le_list (t :: x) (a :: y) -> ~Vertices.E.lt t a /\ (Vertices.E.eq t a /\ ~le_list x y \/ ~Vertices.E.eq t a).
  Proof.
    intros.
    destruct (ordV.ME.lt_dec t a).
    exfalso.
    auto.
    split.
    auto.
    destruct (Vertices.E.eq_dec t a);
    auto.
    left.
    split; auto.
  Qed.

  Lemma not_le_lt_rev : forall x y, ~ le_list x y -> ord.lt_list y x.
    Proof.
      intros.
      generalize dependent x.
      induction y.
      intros.
      destruct x.
      exfalso.
      apply H. 
      constructor.
      constructor.
      intros.
      destruct x.    
      exfalso.
      apply H.
      constructor.
      apply helper in H.
      destruct H.
      destruct H0.
      destruct H0.
      constructor 3; auto.
      symmetry.
      auto.
      destruct (Vertices.E.compare_spec a t);
      auto.
      exfalso.
      apply H0.
      symmetry.
      auto.
      contradiction.
    Qed.

    Definition subset_list X Y := forall x , InA Vertices.E.eq x X -> InA Vertices.E.eq x Y.

    Hint Unfold subset_list.
    Hint Resolve Vertices.add_spec.

  Lemma to_list : forall l, Sorted Vertices.E.lt l ->
                            exists s, eqlistA Vertices.E.eq l (Vertices.elements s).
  Proof.
    intros.
    exists (ordV.P.of_list l).
    assert ( equivlistA Vertices.E.eq (ordV.P.to_list (ordV.P.of_list l)) l).
    apply ordV.P.of_list_2.
    apply ordV.sort_equivlistA_eqlistA.
    auto.
    apply Vertices.elements_spec2.
    symmetry.
    auto.
  Qed.


   Module ordDec := WDecide Vertices.
   Import ordDec.


    Lemma lt_witness_list : forall X Y,
        let X' := ordV.P.of_list X in
        let Y' := ordV.P.of_list Y in 
        ord.lt_list X Y -> subset_list X Y \/ exists x,
      InA Vertices.E.eq x (Vertices.elements (Vertices.diff Y' X')) /\            (forall y, InA Vertices.E.eq y
          (Vertices.elements (Vertices.diff Y' X')) ->
                               Vertices.E.lt x y).
  Proof.
    intros.
    unfold X',Y'.
    clear X'.
    clear Y'.
    generalize dependent X.
    generalize dependent Y.
    intros.
    induction H; unfold subset_list;
      [left; intros; si |  | ].
    {
      right.
      exists y.
      split.
      rewrite Vertices.elements_spec1 in *.      
      apply Vertices.diff_spec.
      simpl.
      intuition.
      admit.
      intros.
      rewrite Vertices.elements_spec1 in *.      
      (* this case is easy *)
      admit.
    }
    destruct IHlt_list.
    left.
    intros.
    unfold subset_list in H1.
    +
        inversion H2.
        *
          subst.
          rewrite H4.
          rewrite H.
          auto.
        *
          subst.
          constructor 2.
          auto.
    +
      destruct H1.
      right.
      exists x0.
      destruct H1.
      split.
      *
        rewrite Vertices.elements_spec1 in *.
        apply Vertices.diff_spec.
        split.
        apply Vertices.diff_spec in H1.
        intuition.
        simpl in *.
        apply Vertices.add_spec.
        auto.
        intros Hnot.
        simpl in Hnot.
        apply Vertices.add_spec in Hnot.
        destruct Hnot.
        specialize (H2 x0).
        rewrite Vertices.elements_spec1 in *.
        apply H2 in H1.
        eapply ordV.ME.lt_irrefl; eauto.
        apply Vertices.diff_spec in H1.
        destruct H1.
        contradiction.
      *
        intros.
        apply H2 in H1.
        exfalso.
        eapply ordV.ME.lt_irrefl; eauto.
  Admitted.

  Lemma sublist_iff : forall X Y, subset_list (Vertices.elements X) (Vertices.elements Y) <-> Vertices.Subset X Y.
  Proof.
    split; intros.
    unfold Vertices.Subset.
    unfold subset_list in H.
    intros.
    specialize (H a).
    do 2 rewrite Vertices.elements_spec1 in *.
    auto.
    unfold subset_list.
    intros.
    rewrite Vertices.elements_spec1 in *.
    auto.
  Qed.


  Lemma lt_witness : forall X Y, lt_set X Y -> Vertices.Subset X Y \/ exists x,  Vertices.In x (Vertices.diff Y X) /\ (forall y, Vertices.In y (Vertices.diff Y X) ->  Vertices.E.lt x y).
  Proof.
    intros.
    unfold lt_set in H.
    apply lt_witness_list in H.
    destruct H.
    left.
    apply sublist_iff. auto.
    destruct H.
    destruct H.
    right.
    exists x.
    rewrite Vertices.elements_spec1 in *.
    intros.
    split.
    do 2 rewrite ordV.P.of_list_3 in H.
    auto.
    intros.
    specialize (H0 y).
    rewrite Vertices.elements_spec1 in *.
    do 2 rewrite ordV.P.of_list_3 in H0.
    auto.
  Qed.

End SetOrd.