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

End SetOrd.