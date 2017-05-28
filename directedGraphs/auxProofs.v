Require Import IndependentSets SetOrdering MSets SimpleUndirectedGraphs.
(* Lower level proofs for MaximalIndependentSets *)

Module auxproofs (SG : SimpleUndirectedGraphs).
(* probably too many imports here.  I'll clean things up after 
   the proofs are done *)
  Module ind :=  (independentSets SG).
  Import ind.
  Import SG.
  Module Import vOTF := OrderedTypeFacts Vertices.E.
  Require Import Sorting.
  Module ordDec := WDecide Vertices.
  Import ordDec.
  Module ordV := OrdProperties Vertices.
  Module ord := MakeSetOrdering Vertices.E Vertices.
  Module Import mo := ord.MO.
  
  Module ordL := MakeListOrdering Vertices.E.
  Module Import SetO := SetOrd Vertices.
  Require Import List.
  Import ListNotations.
  
  Theorem elementsList_eq : forall s1 s2,
      Vertices.eq s1 s2 <-> eqlistA Vertices.E.eq (Vertices.elements s1) (Vertices.elements s2).
  Proof.
    split;
      intros.
    {
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
    }
    {
      inversion H;
      subst.
      assert (Vertices.elements s1 = [] /\ Vertices.elements s2 = [])
             by auto.
      intuition.
      rewrite <- ordV.P.elements_Empty in *.
      rewrite ordV.P.empty_is_empty_1; auto.
      apply  ordV.P.empty_is_empty_1 in H4; auto.
      rewrite H4; reflexivity.
      intros v.
      split; intros;
      rewrite ordV.P.Dec.F.elements_iff in *;
      rewrite <- H0 in *;
      rewrite <- H1 in *;
      clear H0; clear H1;
        [rewrite <- H2;
         rewrite <- H3 | rewrite H2; rewrite H3]; auto.
    }
  Qed.

  Lemma listIn : forall x V, Vertices.In x V -> exists y, y = x /\ Vertices.In y V.
  Proof.
    intros.
    exists x.
    split.
    auto.
    auto.
  Qed.


  Lemma sort_subs : forall l1 l2, Sorted Vertices.E.lt (l1 ++ l2) -> Sorted Vertices.E.lt l1 /\ Sorted Vertices.E.lt l2.
  Proof.
    intros.
    split.
    induction l1.
    constructor.
    inversion H.
    constructor.
    apply IHl1.
    auto.
    destruct l1.
    constructor.
    inversion H3.
    constructor.
    auto.
    generalize dependent l2.
    induction l1; intros.
    simpl in H.
    auto.
    inversion H.
    apply IHl1.
    auto.
  Qed.

  Lemma sorted_sort : forall x0 x1 x2, Sorted Vertices.E.lt (x0 ++ x1 :: x2) -> Sorted Vertices.E.lt x0 /\ Sorted Vertices.E.lt x2.
  Proof.
    intros.
    apply sort_subs in H.
    intuition.
    inversion H1.
    auto.
  Qed.


  Lemma equivA_elements : forall V y x, x = y /\ InA Vertices.E.eq y (Vertices.elements V) -> exists s1 s2, equivlistA Vertices.E.eq (Vertices.elements V)((Vertices.elements s1) ++  x :: (Vertices.elements s2)).
  Proof.
    intros.
    assert ( exists l1 z l2, y =v=z /\ Vertices.elements V =
                                       l1 ++ z :: l2).
    apply InA_split.
    intuition.
    do 3 destruct H0.
    exists (ordV.P.of_list x0).
    intuition.
    (*    exists x1.*)
    exists (ordV.P.of_list x2).
    assert (equivlistA Vertices.E.eq (Vertices.elements (ordV.P.of_list x0)) x0).
    apply  ordV.P.of_list_2.
    assert (equivlistA Vertices.E.eq (Vertices.elements (ordV.P.of_list x2)) x2).
    apply ordV.P.of_list_2.
    rewrite H4.
    rewrite H0.
    rewrite H3.
    rewrite H1.
    rewrite H.
    reflexivity.
  Qed.


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

  Lemma list_decomp : forall V y x, x = y /\ InA Vertices.E.eq y (Vertices.elements V) -> exists s1 s2, eqlistA Vertices.E.eq (Vertices.elements V) ((Vertices.elements s1) ++  x :: (Vertices.elements s2)).
  Proof.
    intros.
    assert (exists (l1 : list vertex) (y : vertex) (l2 : list vertex),
               x =v= y /\ Vertices.elements V = l1 ++ y :: l2).
    apply InA_split.
    intuition.
    rewrite H0.
    auto.
    do 4 destruct H0.
    assert (Sorted Vertices.E.lt (x0 ++ x1 :: x2)).
    rewrite <- H1.
    apply Vertices.elements_spec2.
    apply sorted_sort in H2.
    assert (exists s, eqlistA Vertices.E.eq x0 (Vertices.elements s)).
    apply to_list.
    intuition.
    assert (exists s, eqlistA Vertices.E.eq x2 (Vertices.elements s)).
    apply to_list.
    intuition.
    destruct H3, H4.
    exists x3.
    exists x4.
    rewrite H1.
    apply eqlistA_app.
    apply Vertices.E.eq_equiv.
    auto.
    constructor.
    symmetry; auto.
    auto.
  Qed.

  Add Morphism (Sorted Vertices.E.lt)
      with signature  (eqlistA Vertices.E.eq) ==> iff
        as sortedEqlistA_morph.
  Proof.
    split.
    generalize dependent x.
    induction y.
    constructor.
    intros.
    destruct x.
    inversion H.
    inversion H.
    subst.
    constructor.
    apply IHy with (x := x); auto.
    inversion H0.
    auto.
    inversion H0.
    subst.
    rewrite <- H4.
    rewrite <- H6.
    auto.
    +
      generalize dependent y.
      induction x.
      constructor.
      intros.
      destruct y.
      inversion H.
      inversion H.
      subst.
      constructor.
      apply IHx with (y := y); auto.
      inversion H0.
      auto.
      inversion H0.
      subst.
      rewrite H4.
      rewrite H6.
      auto.
  Qed.


  (* Lemma hd_app_decomp : forall x l l', *)
  (*     Sorted Vertices.E.lt l -> Sorted Vertices.E.lt l' -> *)
  (*     HdRel Vertices.E.lt x (l ++ l') -> HdRel Vertices.E.lt x l' /\ HdRel Vertices.E.lt x l. *)
  (* Proof. *)
  (*   intros. *)
  (*   split. *)
  (*   induction l; intros; *)
  (*   auto. *)
  (*   apply IHl; auto. *)
  (*   admit. *)
  (*   apply Sorted_inv in H.  *)
  (*   destruct H. *)
  (*   inversion H1. *)
  (*   subst. *)


  (*   inversion H0. *)
  (*   subst. *)
  (*   constructor. *)
  (*   inv *)


  Lemma mon_aux_equivlistA_eq_app :
    forall   x0 x1 v V, Vertices.In v V
  -> eqlistA Vertices.E.eq (Vertices.elements V)
         (Vertices.elements x0 ++ v :: Vertices.elements x1)
 -> Sorted Vertices.E.lt
        (Vertices.elements x0 ++ v :: Vertices.elements x1) ->
  V =V= Vertices.union x1 (Vertices.add v x0).
  Proof.
    intros.
    apply eqlistA_equivlistA in H0; auto.
    split; intros.
    +
      unfold equivlistA in H0.
      rewrite ordV.P.Dec.F.elements_iff in H2.
      apply H0 in H2.
      apply Vertices.union_spec.
      apply InA_app in H2.
      destruct H2.
      *
        right.
        apply Vertices.add_spec.
        right.
        apply ordV.P.Dec.F.elements_iff.
        auto.
      *
        inversion H2;
          subst.
        { right; apply Vertices.add_spec; auto. }
        { left; apply ordV.P.Dec.F.elements_iff; auto. }
    +
      apply Vertices.union_spec in H2.
      destruct H2; rewrite ordV.P.Dec.F.elements_iff;
        rewrite H0; apply InA_app_iff.
      *
        right. 
        constructor 2.
        rewrite <- ordV.P.Dec.F.elements_iff; auto.
      *
        apply Vertices.add_spec in H2.
        destruct H2;
          [right; rewrite H2; constructor 1 |
           left; apply ordV.P.Dec.F.elements_iff]; auto.
  Qed.





(* This should be changed to say that l ++ l' has no dups you probably 
   need to know that. NoDupA Vertices.E.eq (l ++ l') *)

  Lemma more_sorting : forall x y l l', NoDupA Vertices.E.eq (l ++ l') -> Sorted Vertices.E.lt (l ++ l') -> InA Vertices.E.eq x l -> InA Vertices.E.eq y l' -> Vertices.E.lt x y. 
  Proof.
    intros.
    inversion H0;
    subst.
    assert (l ++ l' = []) by (symmetry; auto).
    apply app_eq_nil in H3; intuition; subst; si.
  Admitted.


End auxproofs.




