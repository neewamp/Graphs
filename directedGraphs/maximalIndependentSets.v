Require Import independentSets.
Import DirectedGraphs_morph SimpleUndirectedGraphs.
Import MSets.

Module maximalIndSets (DG : SimpleUndirectedGraphs).
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

  Definition MkMaximalIndSet (X : Vertices.t) (G : t)
    : Vertices.t :=
    Vertices.fold (fun x X' =>
                     if indSet (Vertices.add x X') G 
                                 then
                       (Vertices.add x X') else X') (enumVertices G) X.
  
  Theorem MkMaximalIndSet_spec : forall X G,
      IndSet X G -> IndSet (MkMaximalIndSet X G) G.
  Proof.
    intros X G H.
    unfold MkMaximalIndSet.
    apply DG_Facts.VertProperties.P.fold_rec_weak; intros; auto.
        destruct (indSet (Vertices.add x a) G) eqn:H4;
      try apply indSet_true_iff in H4;
      auto.
        destruct (indSet_true_iff (Vertices.add x a) G); auto.
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
      apply indSet_true_iff.
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

    destruct (indSet_true_iff (Vertices.add x0 x1) x).
    destruct (indSet_true_iff (Vertices.add y0 y1) y); try si.
    rewrite H,H0,H1 in i.
    si.
    si.
    destruct (indSet_true_iff (Vertices.add x0 x1) x).
    destruct (indSet_true_iff (Vertices.add y0 y1) y). try si.
    si.
    destruct (indSet_true_iff (Vertices.add y0 y1) y).
    rewrite H,H0,H1 in n.
    si.
    si.
  Qed.

  Theorem MkMaximalIndSet_mon : forall V X G, exists X',
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


    Lemma list_cons A : forall (l: list A), (exists x l', l = x :: l') \/ l = [].
      Proof.
        intros.
        induction l; auto.
        destruct IHl.
        do 2 destruct H.
        left.
        exists a,l.
        auto.
        left.
        exists a, l.
        auto.
      Qed.

    Lemma sort_subs : forall l1 l2, Sorted Vertices.E.lt (l1 ++ l2) -> Sorted Vertices.E.lt l1 /\ Sorted Vertices.E.lt l2.
      Proof.
        intros.
        split.
        induction l1.
        admit.
        inversion H.
        constructor.
        apply IHl1.
        auto.
        destruct l1.
        constructor.
        inversion H3.
        constructor.
        auto.

        apply HdRel_inv in H3.

        admit.
        
        inversion H.
        admit.
        

        Admitted.

    Lemma sorted_sort : forall x0 x1 x2, Sorted Vertices.E.lt (x0 ++ x1 :: x2) -> Sorted Vertices.E.lt x0 /\ Sorted Vertices.E.lt x2.
    Proof.
      intros.
      apply Sorted_LocallySorted_iff in H.
      split.
      induction x0.
      constructor.
      apply Sorted_LocallySorted_iff in H.
      apply Sorted_inv with (l := x0 ++ x1 :: x2) in H.
      destruct H.
      apply Sorted_LocallySorted_iff in H. 
      constructor. admit.      
(*       eapply HdRel_inv in H0. *)
      

(* admit. *)
(*       induction x2. *)
(*       constructor. *)
(*       constructor. *)
(*       apply IHx2. *)
(*       inversion H. *)
(*       admit. *)
(*       admit. *)
(*       apply Sorted_LocallySorted_iff in H. *)
(*       inversion H. *)
      (* admit. *)
      

      (* apply Sorted_LocallySorted_iff. *)
      (* induction x0. *)
      (* constructor. *)
      (* apply Sorted_LocallySorted_iff in H. *)
      (* apply Sorted_LocallySorted_iff. *)
      (* apply Sorted_inv with (l := x0 ++ x1 :: x2) in H. *)
      (* destruct H. *)
      (* induction x2. *)
      (* constructor. *)
      (* apply Sorted_LocallySorted_iff. *)
      (* apply Sorted_LocallySorted_iff in H. *)
      (* auto. *)
    (*   admit. *)
      


    (*   constructor. *)
    (*   apply Sorted_LocallySorted_iff. *)
    (*   apply IHx0. *)
    (*   inversion H. *)
    (*   apply Sorted_LocallySorted_iff. *)
    (*   auto. *)
    (*   apply Sorted_inv with (l := x0 ++ x1 :: x2) in H. *)
    (*   destruct H. *)


      
    (*   apply Sorted_LocallySorted_iff in H. *)
      


    (*   admit. *)
    (*   admit. *)
      

    (*   inversion H. *)
    (*   admit. *)
    (*   admit. *)
      


    (* Admitted. *)

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
    assert (exists s, eqlistA Vertices.E.eq x0 (Vertices.elements s)).
    assert (Sorted Vertices.E.lt (x0 ++ x1 :: x2)).
    rewrite <- H1.
    apply Vertices.elements_spec2.
    apply to_list.
    
    admit.
    assert (exists s, eqlistA Vertices.E.eq x2 (Vertices.elements s)).
    apply to_list.
    admit.
    destruct H2, H3.
    exists x3.
    exists x4.
    rewrite H1.
    apply eqlistA_app.
    apply Vertices.E.eq_equiv.
    auto.
    constructor.
    symmetry; auto.
    auto.
  Admitted.

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
    (* apply VertProperties.P.Dec.F.elements_1 in H. *)
    (* apply InA_alt in H. *)
    destruct H.
    assert (exists l1 l2,  eqlistA Vertices.E.eq (Vertices.elements V) ((Vertices.elements l1) ++  x :: (Vertices.elements l2))).
    eapply list_decomp.
    intuition.
    destruct H.
    do 2 destruct H0.
    exists x1,x0.
    rewrite Vertices.fold_spec.
    (* assert (fold_right (growMisStep G) X (rev (Vertices.elements V)) =V=  fold_right (growMisStep G) X (rev ((Vertices.elements x0 ++ x :: Vertices.elements x1)))). *)
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
               (forall x, Vertices.In x X' -> Vertices.E.lt v x) /\
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
  



  Theorem MkMaximalIndSet_mon :forall X G, exists X',
        (MkMaximalIndSet X G) =V= Vertices.union X X'.
  Proof.
    intros X G.
    induction X using ordV.P.set_induction.
    unfold MkMaximalIndSet.
    +
      apply ordV.P.fold_rec_weak; intros; auto.
      exists Vertices.empty.
      rewrite VertProperties.P.empty_union_2; auto; try reflexivity.
      apply VertProperties.P.empty_is_empty_2.
      reflexivity.
      destruct H1.
      rewrite VertProperties.P.empty_union_1 in H1; auto.
    destruct (indSet (Vertices.add x a) G).
    exists (Vertices.add x x0).
    rewrite VertProperties.P.empty_union_1; auto.
    rewrite H1.
    reflexivity.
    exists (x0).
    rewrite VertProperties.P.empty_union_1; auto.
    +

    destruct IHX1.
    exists (x0).
    
    (* rewrite ordV.P.Add_Equal in H0. *)
    (* assert (Vertices.union X2 x0 =V= Vertices.union ((Vertices.add x X1)) x0). *)
    (* rewrite  H0. *)
    (* reflexivity. *)
    (* rewrite H2. *)
    constructor.
    intros.
    unfold Vertices.eq in H1.
    rewrite ordV.P.Add_Equal in H0.
    rewrite  H0.
    rewrite Vertices.union_spec.
        


    admit.
    admit.
    admit.
    Admitted.

  Lemma MkMaximalIndset_add : forall v X G,
      ~ IsVertex v G -> IndSet X (addVertex v G) -> MaximalIndSet (MkMaximalIndSet X G) G
      -> MaximalIndSet (MkMaximalIndSet X (addVertex v G)) (addVertex v G).
  Proof.
    intros.
    assert (MaximalIndSet (MkMaximalIndSet X G) G) by auto.
    (* inversion H1. *)
    (* constructor. *)
    (* constructor. *)
    (* admit. *)
    (* (* contradiction with addVeretex 3*) *)
    (* admit. *)
    (* intros. *)
    (* if x is v or x is not v *)

    apply MaximalIndSet_spec1 with (x := v) in H1.
    (* either indSet X (add v) or not *)
    destruct H1.
    + (* v is not in G so no*)
      unfold MkMaximalIndSet in H1.
      admit.
    +
      (* If that's not an independet set v would not be added and things
         Would still be maximal *)
      Admitted.

  Theorem MkMaximalIndSet_max : forall X G,
      IndSet X G -> MaximalIndSet (MkMaximalIndSet X G) G.
  Proof.
    intros.



Definition LFMIS (G : t) (inp : Vertices.t) : Vertices.t -> Prop :=
  fun (x : Vertices.t) =>  (MkMaximalIndSet inp G) =V= x.

Definition LFMIS_bool (G : t) (inp : Vertices.t) : Vertices.t -> bool :=
  fun( x : Vertices.t) => Vertices.equal (MkMaximalIndSet inp G) x.

Definition isMIS G l :=  LFMIS_bool G l l.

Definition IsMis G l := LFMIS G l l.

Definition LiftGraph (V : Vertices.E.t) (G : t) := G.

Definition mkC_aux V' l G : list Vertices.t:=
  match l with
  | nil => Vertices.empty :: nil
  | cons cand l' =>
    let newS := (Vertices.add V' cand)in
    if independentSet newS G
    then newS ::nil
    else
      if isMIS G ( Vertices.add V' (DG_Facts.rmvNeighbors V' G cand))  then
        if LFMIS_bool (LiftGraph V' G) (DG_Facts.rmvNeighbors V' G cand) cand
        then (Vertices.add V' (DG_Facts.rmvNeighbors V' G cand)) :: cand :: nil
        else  cand :: nil
      else cand :: nil
  end.
