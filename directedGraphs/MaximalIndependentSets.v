Require Import IndependentSets SetOrdering auxProofs.
Import DirectedGraphs_morph SimpleUndirectedGraphs .
Import MSets.

Module MaximalIndSets (DG : SimpleUndirectedGraphs).
   Module ind :=  (independentSets DG).
   Import ind.
   Import DG.
   Import DG_Facts.
   Module Import vOTF := OrderedTypeFacts Vertices.E.
   Require Import Sorting.
   Module ordDec := WDecide Vertices.
   Import ordDec.

   (*   Module SProp := WProperties S. *)
   (*   Module SFacts := WFacts S. *)
  Require Import List.
  Import ListNotations.

  Module ordV := OrdProperties Vertices.
  Module ord := MakeSetOrdering Vertices.E Vertices.
  Module Import mo := ord.MO.

  Module ordL := MakeListOrdering Vertices.E.
  Module Import SetO := SetOrd Vertices.
  
  Module auxp := auxproofs DG.
  Import auxp.


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

  Lemma MaximalIndSet_spec : forall x Y G, MaximalIndSet Y G ->Vertices.In x Y -> Vertices.In x (enumVertices G).
   Proof.
     intros.
     inversion H.
     inversion H1.
     unfold ValidSet in H3.
     apply H3.
     auto.
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
  

  Theorem fold_decomp_spec : forall v V X G, Vertices.In v V ->
    exists X' X'', growMis V X G =V=
                   growMis X' ((growMisStep G) v (growMis X'' X G)) G /\
                   V =V= Vertices.union X' (Vertices.add v X'') /\
             (forall x, Vertices.In x X'' 
                        -> Vertices.E.lt x v /\ Vertices.In x V).         Proof.
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
    split.
    rewrite Vertices.fold_spec.
    rewrite fold_equivlistLeft with (s' := (Vertices.elements x0 ++ x :: Vertices.elements x1)); auto.
    rewrite fold_left_app.
    rewrite fold_left_decomp.
    rewrite <- Vertices.fold_spec.
    rewrite <- Vertices.fold_spec.
    rewrite H.
    reflexivity.
    intros.
    subst.
    assert (Sorted Vertices.E.lt (Vertices.elements x0 ++ v :: Vertices.elements x1)).
    rewrite <- H0.
    auto.
    split; intros.
    rewrite <- ordV.P.of_list_3.
    unfold ordV.P.to_list.
    (* a morphism for this would be nice *)
    (* apply elementsList_eq_iff in H0. *)
    admit.
    Admitted.

  Theorem fold_decomp : forall v V X G, Vertices.In v V ->
      exists X' X'', growMis V X G =V=
               growMis X' ((growMisStep G) v (growMis X'' X G)) G.
  Proof.
    intros.
    edestruct (fold_decomp_spec); eauto.
    destruct H0.
    destruct H0.
    eauto.
  Qed.

  (* Add Morphism growMis *)
  (*     with signature  Vertices.eq ==> Vertices.eq ==> EqualGraph ==> Vertices.eq *)
  (*       as growMis_morph. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold growMis. *)
  (*   rewrite  VertProperties.P.fold_init with (eqA := Vertices.eq); eauto. *)
  (*    do 2 rewrite Vertices.fold_spec. *)
  (*   rewrite elementsList_eq_iff in H. *)
  (*   rewrite fold_equivlistLeft; eauto. *)
  (*   do 2 rewrite <- Vertices.fold_spec. *)
  (*  admit. *)
  (*   unfold Proper. *)
  (*   unfold respectful. *)
  (*   intros. *)
  (*   rewrite H3. *)
  (*   rewrite H2. *)
  (*   reflexivity. *)
  (* Admitted. *)



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


  Lemma MkMaximalIndSet_spec4 : forall X G, Vertices.Subset X (MkMaximalIndSet X G).
 Proof.
   intros.
   intros x  H.
   destruct (MkMaximalIndSet_mon X G).
   rewrite H0.
   rewrite Vertices.union_spec.
   auto.
 Qed.


 Lemma MkMaximalIndSet_subset : forall X Y G, MaximalIndSet X G -> MaximalIndSet Y G -> Vertices.Subset X Y -> (Vertices.Subset Y (MkMaximalIndSet X G)).
 Proof.
   intros.
   eapply MaximalIndSet_subs with (G := G)in H1; eauto.
   destruct (MkMaximalIndSet_mon X G).
   rewrite H2.
   intros v H3.
   apply Vertices.union_spec.
   rewrite H1.
   auto.
 Qed.

 Definition eleSub X Y := forall x , InA Vertices.E.eq x (Vertices.elements X) -> InA Vertices.E.eq x (Vertices.elements Y).

 Definition subset_list X Y := forall x , InA Vertices.E.eq x X -> InA Vertices.E.eq x Y.
  
 Lemma subs_elements : forall X Y ,
     Vertices.Subset X Y -> eleSub X Y.
   Proof.
     intros.
     unfold eleSub.
     unfold Vertices.Subset in H.
     intros.
     apply ordV.P.Dec.F.elements_iff  with (x := x) in H; auto.
     rewrite <- VertProperties.P.Dec.F.elements_iff in H0.
     auto.
   Qed.

   Lemma  not_le_lt_set : forall X Y, ~ le_set X Y ->
                                      lt_set Y X.
   Proof.
     intros.
     apply not_le_lt_rev in H.
     auto.
   Qed.


   Lemma help : forall X,
       (exists x , Vertices.In x X) \/ Vertices.Empty X.
   Proof.
     intros.
     induction X using ordV.P.set_induction; eauto.
     destruct IHX1.
     destruct H1;
     apply ordV.P.Add_Equal in H0.
     left.
     exists x0.
     rewrite H0.
     rewrite Vertices.add_spec.
     auto.
     left.
     exists x.
     apply ordV.P.Add_Equal in H0.
     rewrite H0.
     rewrite Vertices.add_spec.
     auto.
   Qed.

   Lemma indset_singleton : forall x G,
       Vertices.In x (enumVertices G) -> IndSet (Vertices.singleton x) G.
     Proof.
       intros.
       constructor.
       intros x0 H0; auto.
       apply ordV.P.Dec.F.singleton_1 in H0.
       rewrite <- H0.
       auto.
       intros x0 x1 H0 H1.
       apply ordV.P.Dec.F.singleton_1 in H0.
       apply ordV.P.Dec.F.singleton_1 in H1.
       rewrite <- H0,H1.
       rewrite <- IsEdgeEnum.
       apply edges_irreflexive.
     Qed.
     

     Lemma ahhhh : forall X Y G,
         MaximalIndSet (ordV.P.of_list X) G -> MaximalIndSet (ordV.P.of_list Y) G -> ord.lt_list X Y -> X <> [] /\ Y <> [].
     Proof.
       intros.
       destruct X;
       destruct Y.
       inversion H1.
       inversion H.
       assert (IndSet (Vertices.add e (ordV.P.of_list [])) G).
       { simpl.  rewrite <- ordV.P.singleton_equal_add.
         apply indset_singleton.
         assert (InA Vertices.E.eq e (Vertices.elements (ordV.P.of_list (e :: Y)))).
         rewrite <- ordV.P.Dec.F.elements_iff.
         simpl.
         apply Vertices.add_spec.
         auto.
         eapply MaximalIndSet_spec; eauto.
         apply  <- ordV.P.Dec.F.elements_iff in H4.
         auto.
       }
       inversion H.
       apply H6 in H4.
       simpl in H4.
       apply ordV.P.Dec.F.empty_iff in H4.
       destruct H4.
       inversion H1.
       split; intros Hnot; inversion Hnot.
     Qed.

   Lemma notIn_notInd : forall x2 X G x,
       Vertices.In x x2 -> 
       ~ Vertices.In x (growMis x2 X G) -> exists X',
  ~IndSet (Vertices.add x X') G /\ Vertices.Subset X' (growMis x2 X G).
   Proof.
     intros.
     destruct (MkMaximalIndSet'_mon x2 X G).
     unfold growMis in H.
     destruct (fold_decomp_spec x x2 X G); auto.
     do 2 destruct H2.
     destruct H3.
     unfold growMisStep in H2.
     destruct (indSet (Vertices.add x (growMis x3 X G))) eqn:H5.
     -
       rewrite H2 in H0.
       exfalso.
       apply H0.
       destruct (MkMaximalIndSet'_mon x1 (Vertices.add x (growMis x3 X G)) G).
       rewrite H6.
       apply Vertices.union_spec.
       rewrite Vertices.add_spec.
       auto.
     -
       exists (growMis x3 X G).
       split.
       destruct (indSet_reflect (Vertices.add x (growMis x3 X G)) G);
         try si; auto.
       rewrite H2.
       destruct (MkMaximalIndSet'_mon x1 (growMis x3 X G) G).
       rewrite H6.
       intros x' H7.
       apply Vertices.union_spec.
       auto.
   Qed.

     Lemma and_reflect : forall a b, reflect (a=true /\ b=true) (a && b) .
     Proof.
       intros.
       apply iff_reflect.
       symmetry.
       apply andb_true_iff.
     Qed.

     Lemma not_ind : forall X G,
         ~IndSet X G -> ~IndependentSet X G \/ ~ ValidSet X G.
     Proof.
       intros.
       destruct (help X).
       destruct H0.
       destruct (IsVertex_reflect G x).
       left.
       intros Hnot.
       apply H.
       constructor.
       unfold ValidSet.
       intros.
       admit.
       auto.
       right. admit.
       admit.
       Admitted.


     Lemma not_indep : forall x  X G,
         IndependentSet X G -> 
         ~ IndependentSet (Vertices.add x X) G ->
         exists z, Edges.In (buildEdge x z) (enumEdges G) /\
                   Vertices.In z X.
     Proof.
       Admitted.

     
     (* Ltac graphind1  G := *)
     (*   match goal with *)
     (*   | [ G : t |- ?G1 ] => *)
     (*     set (fun G' : t=> (replace G with G' in G1)) as P; idtac G *)
     (*   end. *)

     Lemma not_ind_witness : forall x X G ,
         IndSet X G -> IsVertex x G ->
         ~ IndSet (Vertices.add x X) G ->
       exists z : vertex,
  Vertices.In z X /\ Edges.In (buildEdge x z) (enumEdges G).
   Proof.
     intros.
     generalize dependent G.
     (* set (fun G => exists z : vertex, *)
     (* Vertices.In z X /\ Edges.In (buildEdge x z) (enumEdges G)). *)
     (* change (P G). *)
     intros G.
     Ltac graphind1 G :=
       match goal with
       | [ |- context [?P  ?g]] => let G := fresh "G" in
                                 set (fun G : t=> P)
       end.
       (*   set (fun G' : t=> change G with G') as P; idtac G *)
       (* end. *)
     graphind1 G.

     
     


     set (fun G => IndSet X G ->
   IsVertex x G ->
   ~ IndSet (Vertices.add x X) G ->
   exists z : vertex,
     Vertices.In z X /\ Edges.In (buildEdge x z) (enumEdges G)).
     change (P G).
     apply DG_Facts.ind3.
     admit.
     unfold P.
     intros.
     admit.
     unfold P.
     intros.
     admit.
     intros.
     unfold P in *.
     intros.
     



     intros.
     

     apply not_ind in H1.
     destruct H1.
     

     
     unfold IndependentSet in H1.
     




     assert (forall X G, IndSet X G -> IndependentSet X G /\ ValidSet X G).
     admit.
     specialize (H2 (Vertices.add x X) G).
     assert (~ IndependentSet (Vertices.add x X) G).
     intros Hnot.
     apply H1.
     apply H2.



     do 2 destruct H.
     exists x1.
     split; auto.
     rewrite H3.
     rewrite Vertices.add_spec.
     auto.
     rewrite H3 in H1.
     intros Hnot.
     apply H1.
     clear IHX1.
     clear H1.
     





     Admitted.

   Lemma max_edge_contra : forall x x3 G Y, MaximalIndSet Y G ->
       Edges.In (buildEdge x x3) (enumEdges G)
                -> Vertices.In x3 Y -> Vertices.In x Y -> False.
   Proof.
     intros.
     inversion H.
     inversion H3.
     unfold IndependentSet in H6.
     specialize (H6 x x3).
     apply H6; auto.
   Qed.

   Lemma grow_mis_spec : forall x x2 X G,
       Vertices.In x (growMis x2 X G) ->
       Vertices.In x x2 \/ Vertices.In x X.
   Proof.
     intros.
     (* I need to know that x2 is a subset of the vertices. *)
     Admitted.

   Theorem MkMaximalIndSet_spec3 : forall X Y G,
       IndSet X G -> MaximalIndSet Y G -> Vertices.Subset X Y ->
       le_set (MkMaximalIndSet X G) Y.
   Proof.
     intros.
     destruct (le_setReflect (MkMaximalIndSet X G) Y); auto.
     apply not_le_lt_set in n.
     assert (MaximalIndSet (MkMaximalIndSet X G) G).
     apply MkMaximalIndSet_max.
     auto.
     assert (H3 : lt_set Y (MkMaximalIndSet X G)) by auto.
     eapply lt_witness in n; eauto.
     destruct n.
     {
       inversion H0.
       apply le_set_spec.
       left.
       symmetry.
       eapply MaximalIndSet_subs; eauto.
     }
     {
       destruct H4.
       destruct H4.
       (* destruct (ordV.P.In_dec x (Vertices.diff (MkMaximalIndSet X G) Y)). *)
       destruct (help (Vertices.diff (MkMaximalIndSet X G) Y)).
       -
         destruct H6.
         assert (Vertices.In x0 (Vertices.diff (MkMaximalIndSet X G) Y))
           by auto.
         apply H5 in H6.
         rewrite Vertices.diff_spec in *.
         destruct (fold_decomp_spec x (enumVertices G) X G); auto.
         eapply MaximalIndSet_spec with (Y := Y); eauto; intuition.
         destruct H8.
         destruct H8.
         assert (H20 : lt_set Y (MkMaximalIndSet X G)) by auto.
         rewrite H8 in H3.
         unfold growMisStep in H3.
         case_eq (indSet (Vertices.add x (growMis x2 X G)) G).
         +
           intros.
           assert ( Vertices.In x (MkMaximalIndSet X G)).
           rewrite H8.
           unfold growMisStep.
           rewrite H10.
           destruct (MkMaximalIndSet'_mon x1  (Vertices.add x (growMis x2 X G)) G).
           rewrite H11.
           apply Vertices.union_spec.
           rewrite  Vertices.add_spec.
           auto.
           destruct H4.
           contradiction.
         +
           intros.
           (* x \in output *)
           (* find a z in (growMis x2 X G) that  *)
           assert (exists z, Vertices.In z (growMis x2 X G) /\
                             ~Vertices.In z Y).
           destruct (not_ind_witness x x2 X G).
           (* any subset of the output should be an Indset *)
           admit.
           destruct (indSet_reflect (Vertices.add x (growMis x2 X G)) G);
             try si.
           destruct H11.
           exists x3.
           split; auto.
           intros Hnot.
           

           (* find the witness that makes adding x to growMis x2 X G not
          an indSet and show that it is in growMis *)
           destruct (indSet_reflect (Vertices.add x (growMis x2 X G)) G).
           try si.
           clear H10.
           apply (max_edge_contra x x3 G Y); destruct H4; auto.
           destruct H11.
           assert (Vertices.In x3 x2).
           

           admit.
           assert (Vertices.In x3 (MkMaximalIndSet X G) /\
                   ~ Vertices.In x3 Y).
           {
             rewrite H8.
             destruct H11.
             split; auto.
             destruct (MkMaximalIndSet'_mon x1
                                            (growMisStep G x (growMis x2 X G)) G).
             rewrite H14.
             apply Vertices.union_spec.
             left.
             unfold growMisStep.
             rewrite H10.
             auto.
           }
           rewrite <- Vertices.diff_spec in H13, H4.
           apply H5 in H13.
           destruct H9.
           apply H14 in H12.
           destruct H12.
           assert (StrictOrder Vertices.E.lt).
           apply Vertices.E.lt_strorder.
           exfalso.
           apply StrictOrder_Asymmetric in H13.
           auto.
           auto.
   Admitted.
   
End MaximalIndSets.

(* init first set is empty, list 
   shift : list (sets vert) -> list (sets vert) 
     cons a B -> (mkcs a) ++ B. 
     can only can only be applied when not empty or not last vertex
   dump : list (sets vert) -> list (sets vert) 
   if its' a maximalind of the entire graph and dumps them somewhere.
   terminate : nil -> stuff you have dumped. 
   *)


