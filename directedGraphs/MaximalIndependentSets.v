Require Import independentSets SetOrdering.
Import DirectedGraphs_morph SimpleUndirectedGraphs .
Import MSets.

Module MaximalIndSets (DG : SimpleUndirectedGraphs).
   Module ind :=  (independentSets DG).
   Import ind.
   Import DG.
   Import DG_Facts.
   
   Module ordDec := WDecide Vertices.
   Import ordDec.

   (*   Module SProp := WProperties S. *)
   (*   Module SFacts := WFacts S. *)
  Require Import List.
  Import ListNotations.

  Module ordV := OrdProperties Vertices.
  

  (* Definition of a Maximal Independent Set with respect to a graph *)
  Inductive MaximalIndSet (X : Vertices.t) (G : t) : Prop :=
  | defMaximalIndSet :
      IndSet X G ->
      (forall x, IndSet (Vertices.add x X) G -> Vertices.In x X) ->
      MaximalIndSet X G.
  
  Definition maximalIndSet (X : Vertices.t) (G : t) : bool :=
    indSet X G && Vertices.for_all (fun x => indSet (Vertices.add x X) G && Vertices.mem x X) (enumVertices G). 
  
  Theorem maxIndReflect : forall X G,
      reflect (MaximalIndSet X G) (maximalIndSet X G).
  Proof.
    Admitted.

  (* An equivalent definition *) 
  Inductive MaximalIndSet_contrapos
  (X : Vertices.t) (G : t) : Prop :=
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

  Definition MkMaximalIndSet' (X : Vertices.t) (G : t)
    : Vertices.t :=
    Vertices.fold (fun x X' =>
                     if indSet (Vertices.add x X') G 
                                 then
                       (Vertices.add x X') else X') (enumVertices G) X.
  
  Theorem MkMaximalIndSet'_spec : forall X G,
      IndSet X G -> IndSet (MkMaximalIndSet' X G) G.
  Proof.
    intros X G H.
    unfold MkMaximalIndSet'.
    apply DG_Facts.VertProperties.P.fold_rec_weak; intros; auto.
        destruct (indSet (Vertices.add x a) G) eqn:H4;
      try apply indSet_true_iff in H4;
      auto.
        destruct (indSet_reflect (Vertices.add x a) G); auto.
        inversion H4.
  Qed.
  
  Add Morphism MaximalIndSet
      with signature Vertices.eq ==> EqualGraph ==> iff
        as maxindEq.
  Proof.
    intros.
    split; constructor; intros.
    {
      inversion H1.
      inversion H2; constructor; unfold ValidSet,IndependentSet in *;
      auto.
      intros.
      rewrite  <- H0.
      apply H4.
      rewrite H.
      auto.
      intros.
      rewrite <- H0.
      apply H5.
      rewrite <- H in H6,H7.
      do 2 auto.
      rewrite H.
      auto.
    }
    {
      inversion H1.
      rewrite <- H.
      apply H4.
      inversion H2.
      constructor; unfold ValidSet, IndependentSet in *; intros; auto.
      rewrite H0.
      apply H5.
      rewrite <- H.
      auto.
      rewrite  H0.
      apply H6;
      rewrite <- H; auto.
    }
    {
      inversion H1.
      inversion H2.
      constructor; unfold ValidSet, IndependentSet in *; intros; auto.
      rewrite H0.
      apply H4.
      rewrite <- H.
      auto.
      rewrite H0.
      apply H5;
        rewrite <- H; auto.
    }
    {
      inversion H1.
      rewrite  H.
      apply H4.
      inversion H2.
      constructor; unfold ValidSet, IndependentSet in *; intros; auto.
      rewrite <- H0.
      apply H5.
      rewrite H.
      auto.
      rewrite <-  H0.
      apply H6;
      rewrite  H; auto.
    }
  Qed.

  Lemma MaximalIndSet_spec1 : forall x X G, MaximalIndSet X G -> Vertices.In x X \/ ~ IndSet (Vertices.add x X) G.
  Proof.
    intros.
    assert ({IsVertex x G} + {~IsVertex x G}).
    eapply reflect_dec.
    apply IsVertex_reflect.
    destruct H0.
    +
      assert ({IndSet (Vertices.add x X) G} + {~ IndSet (Vertices.add x X) G}).
      eapply reflect_dec.
      apply indSet_reflect.
      destruct H0; auto.
      inversion H.
      apply H1 in i0.
      auto.
    +
      right.
      intros Hnot.
      inversion Hnot.
      unfold ValidSet in H0.
      specialize (H0 x).
      apply n.
      apply IsVertexEnum.
      apply H0.
      apply Vertices.add_spec.
      left.
      reflexivity.
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

  Definition growMisStep (G : t) (x : vertex) (X : Vertices.t)  :=
    if indSet (Vertices.add x X) G then Vertices.add x X else X.
  
  Definition growMis (V : Vertices.t) (X : Vertices.t) (G : t) :=
    Vertices.fold (growMisStep G) V X.
  
  Definition MkMax (X : Vertices.t) G := growMis (enumVertices G) X.


  Ltac fd :=
    match goal with
    | [ |- ?X =V= ?X ] => reflexivity
    | _ => fsetdec
    end.

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


  Add Morphism growMisStep
      with signature  EqualGraph ==> Vertices.E.eq ==> Vertices.eq ==> Vertices.eq
        as growMisStep_morph.
  Proof.
    intros.
    unfold growMisStep.
    destruct ( indSet (Vertices.add x0 x1) x) eqn: H2;
    destruct ( indSet (Vertices.add y0 y1) y)eqn: H3; try auto; try rewrite H1, H0; try fd try reflexivity; try rewrite <- H1, H0; try fd.

    destruct (indSet_reflect (Vertices.add x0 x1) x).
    destruct (indSet_reflect (Vertices.add y0 y1) y); try si.
    rewrite H,H0,H1 in i.
    si.
    si.
    destruct (indSet_reflect (Vertices.add x0 x1) x).
    destruct (indSet_reflect (Vertices.add y0 y1) y). try si.
    si.
    destruct (indSet_reflect (Vertices.add y0 y1) y).
    rewrite H,H0,H1 in n.
    si.
    si.
  Qed.

  Theorem MkMaximalIndSet'_mon : forall V X G, exists X',
        growMis V X G =V= Vertices.union X X'.
  Proof.
    intros V X G.
    induction V using ordV.P.set_induction.
    exists (Vertices.empty).
    unfold growMis.
    unfold growMisStep.
    rewrite VertProperties.P.fold_1b; try fsetdec.
    rewrite VertProperties.P.empty_union_2; try fsetdec; try reflexivity.
    destruct IHV1.
    unfold growMis.
    apply ordV.P.fold_rec_weak;
    intros; eauto.
    exists (Vertices.empty).
   rewrite VertProperties.P.empty_union_2; try fsetdec; try reflexivity.   
    unfold growMisStep.
    destruct (indSet (Vertices.add x1 a) G); eauto.
    destruct H3.
    exists (Vertices.add x1 x2).
    rewrite H3.
    +
      split; intros; try fsetdec.
  Qed.

  Lemma fold_left_decomp : forall x0 x1 G X,
      fold_left (flip (growMisStep G)) (x0 :: x1) X =
      fold_left (flip (growMisStep G)) (x1) (growMisStep G x0 X).
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Lemma listIn : forall x V, Vertices.In x V -> exists y, y = x /\ Vertices.In y V.
    Proof.
      intros.
      exists x.
      split.
      auto.
      auto.
    Qed.

    Module Import vOTF := OrderedTypeFacts Vertices.E.
    Require Import Sorting.

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

(* init frist set is empty, list 
   shift : list (sets vert) -> list (sets vert) 
     cons a B -> (mkcs a) ++ B. 
     can only can only be applied when not empty or not last vertex
   dump : list (sets vert) -> list (sets vert) 
   if its' a maximalind of the entire graph and dumps them somewhere.
   terminate : nil -> stuff you have dumped. 
*)

  Lemma fold_equivlistLeft : forall G, 
       forall s s' i,
       eqlistA Vertices.E.eq s s' -> Vertices.Equal (fold_left (flip (growMisStep G)) s i) (fold_left (flip (growMisStep G)) s' i).
    Proof.
      intros.
      do 2 rewrite  <- fold_left_rev_right.
      eapply fold_right_eqlistA; eauto.
      apply Vertices.eq_equiv.
      unfold Proper.
      unfold respectful.
      intros.
      rewrite H0.
      rewrite H1.
      reflexivity.
      rewrite H.
      reflexivity.
    Qed.


  Theorem fold_decomp : forall v V X G, Vertices.In v V ->
    exists X' X'', growMis V X G =V=
                   growMis X' ((growMisStep G) v (growMis X'' X G)) G.
  Proof.
    unfold growMis.
    intros.
    apply listIn in H.
    destruct H.
    assert (exists l1 l2,  eqlistA Vertices.E.eq (Vertices.elements V) ((Vertices.elements l1) ++  x :: (Vertices.elements l2))).
    eapply list_decomp.
    intuition.
    destruct H.
    do 2 destruct H0.
    exists x1,x0.
    rewrite Vertices.fold_spec.
    rewrite fold_equivlistLeft with (s' := (Vertices.elements x0 ++ x :: Vertices.elements x1)); auto.
    rewrite fold_left_app.
    rewrite fold_left_decomp.
    rewrite <- Vertices.fold_spec.
    rewrite <- Vertices.fold_spec.
    rewrite H.
    reflexivity.
  Qed.

  Theorem fold_decomp_spec : forall v V X G, Vertices.In v V ->
      exists X' X'', growMis V X G =V=
               growMis X' ((growMisStep G) v (growMis X'' X G)) G /\
               (forall x, Vertices.In x X' -> Vertices.E.lt x v) /\
               (forall x, Vertices.In x X'' -> Vertices.E.lt x v) /\
               (Vertices.union X'(Vertices.add v  X'')) =V= V.
  Proof.
    intros.
    assert (exists X' X'' : Vertices.t,
     growMis V X G =V= growMis X' (growMisStep G v (growMis X'' X G)) G).
    apply fold_decomp.
    auto.
    do 2 destruct H0.
    exists x,x0.
    split.
    auto.
    split.
    intros.
    intros.
    Admitted.
  

(* show that the set is a subset of the vertices.  
   then consider whether a vertex is a member of the set or not *)

  Definition MkMaximalIndSet (X : Vertices.t) (G : t) :=
    growMis (enumVertices G) X G.

  Lemma  Mkequiv : forall X G,
      MkMaximalIndSet X G = MkMaximalIndSet' X G.
  Proof.
    intros.
    unfold MkMaximalIndSet.
    unfold growMis.
    unfold MkMaximalIndSet'.
    unfold growMisStep.
    reflexivity.
  Qed.

  Theorem MkMaximalIndSet_spec : forall X G,
      IndSet X G -> IndSet (MkMaximalIndSet X G) G.
  Proof.
    intros X G H.
    rewrite Mkequiv.
    apply MkMaximalIndSet'_spec.
    auto.
  Qed.

(* Module hi := MakeSetOrdering Vertices. *)

  Theorem MkMaximalIndSet_mon :forall X G, exists X',
        (MkMaximalIndSet X G) =V= Vertices.union X X'.
  Proof.
    intros X G.
    assert (exists X' : Vertices.t, growMis (enumVertices G) X G =V= Vertices.union X X').
    apply MkMaximalIndSet'_mon.
    destruct H.
    exists x.
    auto.
  Qed.

  Lemma sil : forall x0 x x1 X G, exists X', (growMis x0 (Vertices.add x (growMis x1 X G)) G) =V= Vertices.union ((Vertices.add x (growMis x1 X G))) X'.
  Proof.
    intros.
    apply MkMaximalIndSet'_mon.
  Qed.

  Lemma IndSet_grow_decomp : forall x x0 x1 X G, IndSet
         (Vertices.add x (growMis x0 (growMisStep G x (growMis x1 X G)) G)) G -> IndSet (Vertices.add x (growMis x1 X G)) G.
  Proof.
    intros.
    constructor;
      inversion H.
    {
      unfold ValidSet in *.
      intros.
      apply H0; auto.
      apply Vertices.add_spec in H2.
      destruct H2.
      apply Vertices.add_spec.
      intuition.
      assert (exists X', growMis x0 (growMisStep G x (growMis x1 X G)) G =V= Vertices.union (growMisStep G x (growMis x1 X G)) X').
      apply MkMaximalIndSet'_mon.
      destruct H3.
      rewrite H3.
      apply Vertices.add_spec.
      right.
      apply Vertices.union_spec.
      left.
      unfold growMisStep.
      destruct (indSet (Vertices.add x (growMis x1 X G)) G);
        try apply Vertices.add_spec;
        intuition.
    }
    {
      unfold IndependentSet in *.
      intros.
      apply H1; rewrite Vertices.add_spec in *.
      +
        assert (exists X', growMis x0 (growMisStep G x (growMis x1 X G)) G =V= Vertices.union (growMisStep G x (growMis x1 X G)) X') by 
      apply MkMaximalIndSet'_mon;
            destruct H4.
        destruct H2.
        left; auto.
        right.
        rewrite H4.
        apply Vertices.union_spec.
        left;
          unfold growMisStep.
          destruct (indSet (Vertices.add x (growMis x1 X G)) G);
          auto.
          apply Vertices.add_spec.
          intuition.
      +
        assert (exists X', growMis x0 (growMisStep G x (growMis x1 X G)) G =V= Vertices.union (growMisStep G x (growMis x1 X G)) X') by 
      apply MkMaximalIndSet'_mon;
            destruct H4.
        destruct H3.
        intuition.
        right.
        rewrite H4.
        apply Vertices.union_spec.
        left;
          unfold growMisStep.
          destruct (indSet (Vertices.add x (growMis x1 X G)) G);
          auto.
          apply Vertices.add_spec.
          intuition.
    }
  Qed.

  Theorem MkMaximalIndSet_max : forall X G,
      IndSet X G -> MaximalIndSet (MkMaximalIndSet X G) G.
  Proof.
    intros.
    constructor; intros.
    apply MkMaximalIndSet_spec.
    auto.
    assert ({Vertices.In x (MkMaximalIndSet X G)} + {~Vertices.In x (MkMaximalIndSet X G)}).
    apply ordV.P.In_dec.
    destruct H1.
    auto.
    unfold MkMaximalIndSet in *.
    assert (exists X' X'' : Vertices.t,
         growMis (enumVertices G) X G =V=
         growMis X' (growMisStep G x (growMis X'' X G)) G).
    apply fold_decomp.
    assert ({Vertices.In x (enumVertices G)} + {~Vertices.In x (enumVertices G)}).
    apply ordV.P.In_dec.
    destruct H1; auto.
    +
      inversion H0.
      unfold ValidSet in H1.
      apply H1.
      apply Vertices.add_spec.
      intuition.
    +
        do 2 destruct H1.
        rewrite H1 in n.
        unfold growMisStep in n.
        case_eq (indSet (Vertices.add x (growMis x1 X G)) G).
    -
      intros.
      rewrite H2 in n.
      assert ( exists X',
                 (MkMaximalIndSet X G) =V= Vertices.union X X').
      apply MkMaximalIndSet_mon.
      destruct H3.
      unfold MkMaximalIndSet in H3.
      assert (exists X' : Vertices.t,
                 growMis x0 (Vertices.add x (growMis x1 X G)) G =V=
                 Vertices.union (Vertices.add x (growMis x1 X G)) X').
      apply MkMaximalIndSet'_mon.
      destruct H4.
      rewrite H4 in n.
      exfalso.
      apply n.
      apply Vertices.union_spec.
      left.
      apply Vertices.add_spec. intuition.
    -
      intros.
      rewrite H2 in n.
      rewrite H1 in H0.
      apply IndSet_grow_decomp in H0.
      destruct (indSet_reflect ((Vertices.add x (growMis x1 X G))) G);
      si.
  Qed.
    

  (*Given two subset X, Y ⊆ V, such that X , Y, X < Y according to the lexicographic ordering
if and only if the minimum element of X − Y is less than the minimum element of Y − X or
Y − X = ∅.*)

  (* Here begins the lexegraphical ordering *)
  
  Theorem MaximalIndSet_subs : forall X Y G, Vertices.Subset X Y -> MaximalIndSet X G -> MaximalIndSet Y G ->  X =V= Y.
  Proof.
    intros X Y G H0 H1 H2. rewrite  MaximalIndSet_eq in *.
    unfold Vertices.Subset in H0.  intros x. split; intros H3.
    (* -> *)
    apply H0 in H3. apply H3.
    (* <- *)
    assert ({Vertices.In x X} + {~ Vertices.In x X}) as H4. apply ordV.P.In_dec. 
    destruct H4 as [H4| H4]. apply H4.

    assert (False).
    assert (~IndSet (Vertices.add x X) G) as H5. destruct H1 as [H1 H5].    apply H5. apply H4.
    apply H5. constructor. intros y H6.
    apply Vertices.add_spec in H6.
    destruct H6 as [H6 | H6]. apply H2.
    rewrite H6. auto. apply H1. auto.
    intros y z H6 H7. apply H2.
    apply Vertices.add_spec in H6.
    destruct H6 as [H6 | H6].
    rewrite H6. auto. auto. 
    apply Vertices.add_spec in H7.
    destruct H7 as [H7 | H7].
    rewrite H7. auto. apply H0. auto. inversion H.
  Qed.
  

  Theorem IndSet_lift_spec : forall X x G,
      MaximalIndSet X G -> IsVertex x G -> IndSet (Vertices.add x X) G -> Vertices.In x X.
  Proof.
    intros. rewrite -> MaximalIndSet_eq in H. destruct H as [[H2 H3] H4].
    assert ( {Vertices.In x X}+{~Vertices.In x X} ) as H5 by (apply ordV.P.In_dec).
    destruct H5 as [H5 | H5]. assumption.
    exfalso. apply H4 in H5. contradiction.
  Qed.
  

  Theorem neg_incl_witness : forall X Y, ~ Vertices.Subset Y X <-> exists v, Vertices.In v Y /\ ~ Vertices.In v X.
  Proof.
    Admitted.

  Inductive lt_list : list vertex -> list vertex -> Prop :=
    lt_nil : forall (x : vertex ) (s : list vertex),
      lt_list nil (x :: s)
  | lt_cons_lt : forall (x y : vertex) (s s' : list vertex),
      Vertices.E.lt x y ->
      lt_list (x :: s) (y :: s')
  | lt_cons_eq : forall (x y : vertex) (s s' : list vertex),
      x = y ->
      lt_list s s' ->
      lt_list (x :: s) (y :: s').

  Lemma lt_list_dec : forall l l', ~ eqlistA  Vertices.E.eq l l' -> {lt_list l l'} + {lt_list l' l}.
  Proof.
    intros.
  Admitted.
  
  Hint Constructors lt_list.

  Definition lt := lt_list.
  Hint Unfold lt.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    split.
    {
      assert (forall s s', s=s' -> ~lt s s').
      red; intros. induction H0.
      discriminate.
      inversion H; subst.
      apply (StrictOrder_Irreflexive y); auto.
      inversion H; subst; auto.
      intros s Hs. 
      assert (s = s) by reflexivity.
      apply H in H0.
      contradiction.
    }
    {
      intros s s' s'' H; generalize s''; clear s''; elim H.
      intros x l s'' H'; inversion_clear H'; auto.
      intros x x' l l' E s'' H'; inversion_clear H'; auto.
      constructor 2. transitivity x'; auto.
      constructor 2. rewrite <- H0; auto.
      intros.
      inversion_clear H3.
      constructor 2. rewrite H0; auto.
      constructor 3; auto. transitivity y; auto. unfold lt in *; auto.
    }
  Qed.


  Definition lt_set s s' : Prop :=
    lt_list (Vertices.elements s)  (Vertices.elements s').

  Lemma eqLt : forall s s', ~ Vertices.Equal s s' -> Vertices.lt s s' \/ Vertices.lt s' s.
    Proof.
      intros.
      destruct (Vertices.compare_spec s s'); try contradiction; auto.
    Qed.

  Lemma lt_not_eq : forall x y, Vertices.lt x y -> ~ Vertices.eq x y.
  Proof.
    intros x y H Hcontra.
    destruct Vertices.lt_strorder as [X Y].              
    destruct (Vertices.compare_spec x y).
    { rewrite H0 in H; apply (X _ H). }
    { rewrite Hcontra in H0; apply (X _ H0). }
    rewrite Hcontra in H0; apply (X _ H0).      
  Qed.      

  Lemma lt_not : forall s s', Vertices.lt s' s -> ~ Vertices.lt s s'.
  Proof.
    intros.
    intros Hnot.
    assert (StrictOrder Vertices.lt).
    apply Vertices.lt_strorder.
    apply StrictOrder_Asymmetric in H0.
    unfold Asymmetric in H0.
    apply (H0 s' s H Hnot).
  Qed.

  Lemma dec_aux : forall s s', ~ Vertices.lt s' s <-> Vertices.Equal s' s \/ Vertices.lt s s'.
    split;
    intros.
    destruct (Vertices.compare_spec s s'); auto.
    left. symmetry. auto.
    contradiction.
    destruct H.
    intros Hnot.
    apply lt_not_eq in Hnot.
    contradiction.
    apply lt_not.
    auto.
  Qed.

  Lemma lt_decOr : forall s s', Vertices.lt s s' \/ ~ Vertices.lt s s'.
  Proof.
    intros.
    destruct (Vertices.compare_spec s s').
    right.
    apply dec_aux.
    left.
    auto.
    auto.
    apply lt_not in H.
    auto.
  Qed.
      
Module ord := MakeSetOrdering Vertices.E Vertices.
Module Import mo := ord.MO.

Module ordL := MakeListOrdering Vertices.E.


(* I want to build an equivalence class from an arbitrary set.  
   I need to partition the set.  Definition of an equivalence class for the.
   set.
   H :
   norm X = 0 -> X = identity
   eqa X Y -> norm X = norm Y. 
   -------------------------------
   Need some build equivalance.

   forall x y, eqa x y -> eqc x = eqc y.

 *)
Module Import SetO := SetOrd Vertices.

 Theorem MkMaximalIndSet_spec3 : forall X Y G,
    IndSet X G -> MaximalIndSet Y G -> Vertices.Subset X Y ->
    le (MkMaximalIndSet X G) Y.
 Proof.
   intros.
   (* unfold Vertices.Subset in H1. *)
   destruct (compare_le_spec (MkMaximalIndSet X G) Y); unfold le; try contradiction; auto.
   unfold le in H2.
   destruct H2; [left; symmetry; auto | auto].
      


      (* assert ((StrictOrder Vertices.lt)). *)
      (* apply Vertices.lt_strorder. *)
      (* apply StrictOrder_Asymmetric in H3. *)
      (* unfold Asymmetric in H3. *)
      (* unfold Vertices.Subset in H1. *)
      (* destruct (lt_decOr (MkMaximalIndSet X G) Y). *)
      (* exfalso; eauto. *)
      (* assert (MaximalIndSet (MkMaximalIndSet X G) G). *)
      (* apply MkMaximalIndSet_max. *)
      (* auto. *)
      (* eapply MaximalIndSet_subs in H1. *)
      (* admit. *)
   Admitted.
      



End MaximalIndSets.