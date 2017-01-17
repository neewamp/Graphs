Require Import MSets.
Require Import SimpleUndirectedGraphs DirectedGraphs_morph.

(* If things turn out ok in this file it doesn't seem hard to
   integrate everything with maxind *)

Module independentSets (DG : SimpleUndirectedGraphs).
  Import DG.
  Module DG_Facts := DirectedGraphMorph DG.
  Module vert_prop := WProperties (Vertices).
  Module vertFacts := OrderedTypeFacts Vertices.E.
  
  (* Doesn't seem possible without adding something else 
      to the module?  I'll probably look at this problem more in depth 
     later in the week *)
  Add Morphism buildEdge
  with signature Vertices.E.eq ==> Vertices.E.eq ==> Edges.E.eq
    as buildEdge_morph.
  Proof.
    Admitted.

  
  (* Prop and bool definitions of an Independent Set with respect to a 
      Graph 
   *)
  Definition IndependentSet (X : Vertices.t) (G : t) :=
    forall x y, Vertices.In x X -> Vertices.In y X ->
                ~ Edges.In (buildEdge x y) (DG.enumEdges G).

  Definition independentSet (X : Vertices.t) (G : t) :=
    Vertices.for_all (fun v1 => Vertices.for_all
    (fun v2 => negb (Edges.mem (buildEdge v1 v2) (enumEdges G))) X) X.

  (* They are the same.  Will probably change this to reflection later*)
  Theorem independentSet_true_iff :
    forall X G,
  independentSet X G = true <-> IndependentSet X G. 
  Proof.
    unfold independentSet, IndependentSet.
    split; intros.
    intros Hnot.
    apply Vertices.for_all_spec in H.
    unfold Vertices.For_all in H.
    apply H in H0.
    apply Vertices.for_all_spec in H0.
    unfold Vertices.For_all in H0,H1.
    apply H0 in H1.
    apply Edges.mem_spec in Hnot.
    unfold negb in H1.
    rewrite Hnot in H1.
    inversion H1.
    unfold Proper.
    unfold respectful.
    intros.
    rewrite H3.
    reflexivity.
    admit.
    apply Vertices.for_all_spec.
    admit.
    intros x H1.
    apply Vertices.for_all_spec.
    unfold Proper.
    unfold respectful.
    intros.
    rewrite H0. auto.
    intros x1 H2.
    apply H with (x := x) (y := x1) in H1; auto.
    rewrite <- Edges.mem_spec in H1.
    apply negb_true_iff.
    apply not_true_is_false in H1.
    auto.
  Admitted.


  (* The set contains only those vertices that are in G *)
  Definition ValidSet (X : Vertices.t) (G : t) :=
    forall x, Vertices.In x X -> Vertices.In x (DG.enumVertices G).

  Definition validSet (X : Vertices.t) (G : t) : bool :=
    Vertices.for_all (fun x => if Vertices.mem x X then Vertices.mem x (DG.enumVertices G) else true) X.

  Lemma ProperPifProof : forall X G,  Proper (Vertices.E.eq ==> eq)
     (fun x0 : vertex =>
      if Vertices.mem x0 X
      then Vertices.mem x0 (enumVertices G)
      else true).
  Proof.
    unfold Proper.
    unfold respectful.
    intros.
    destruct (Vertices.mem x X) eqn:H3.
    destruct (Vertices.mem y X) eqn:H4.
    rewrite H.
    auto.
    rewrite <- H in H4.
    apply DG_Facts.VertProperties.P.Dec.F.not_mem_iff in H4.
    apply Vertices.mem_spec in H3.
    apply H4 in H3.
    destruct H3.
    rewrite <- H.
    rewrite H3.
    auto.
  Qed.


  Theorem validSet_true_iff : forall X G, validSet X G = true <-> ValidSet X G.
  Proof.
    unfold validSet, ValidSet.
    split; intros; auto.
    {
      apply Vertices.mem_spec.
      apply Vertices.for_all_spec in H.
      unfold Vertices.For_all in H.
      assert( Vertices.In x X) by auto.
      apply H in H0.
      apply Vertices.mem_spec in H1.
      rewrite H1 in H0.
      auto.
      {
        apply ProperPifProof.
      }
    }
    apply Vertices.for_all_spec.
    {
      apply ProperPifProof.
    }
    intros x H1.
    assert (Vertices.In x X) by auto.
    apply H in H0.
    rewrite <- Vertices.mem_spec in H1,H0.
    rewrite H1; auto.
  Qed.
  
  Lemma hello : forall (x : nat), 2 * x = x + x.
  Proof.
    intros.
    destruct x.
    auto.
    simpl.
    rewrite <- plus_n_O.
    auto.
  Qed.
  


  Theorem validSetRecr : 
    forall x (X : Vertices.t) G,
      ValidSet (Vertices.add x X) G -> ValidSet X G.
  Proof.
    unfold ValidSet. intros. 
    apply H.
    apply Vertices.add_spec.
    auto.
  Qed.

  (* An IndSet is an independent set that is valid *)
  Inductive IndSet (X : Vertices.t) (G : t) :=
  | defIndSet : ValidSet X G -> IndependentSet X G -> IndSet X G. 

  Definition indSet (X : Vertices.t) (G : t) : bool :=
    validSet X G && independentSet X G.

  Theorem indSet_true_iff : forall X G, indSet X G = true <-> IndSet X G.
  Proof.
    intros.
    unfold indSet.
    split; try constructor;
      try apply andb_true_iff in H;
      try rewrite validSet_true_iff in H;
      try rewrite independentSet_true_iff in H;
      intuition.
    inversion H.
   rewrite andb_true_iff.
   rewrite validSet_true_iff;
   rewrite independentSet_true_iff; intuition.
  Qed.

  Theorem nilIndSet : IndSet Vertices.empty DG.empty.
  Proof.
    constructor;
      try constructor; try intros x y H; unfold ValidSet; intros;
      try apply vert_prop.Dec.F.empty_iff in H;
      try contradiction.    
  Qed.

  Theorem empty_IndSet_spec : forall G, IndSet Vertices.empty G.
  Proof.
    intros.
    constructor.
    unfold ValidSet.
    intros.
    apply vert_prop.Dec.F.empty_iff in H.
    destruct H.
    unfold IndependentSet.
    intros.
    apply vert_prop.Dec.F.empty_iff in H.
    destruct H.
  Qed.
  
  Theorem nilIndSetAdd : forall x G, Vertices.In x (enumVertices G) ->
                       IndSet (Vertices.add x Vertices.empty) G.
  Proof.
    intros x G H.
    constructor.
    unfold ValidSet.
    intros.
    apply Vertices.add_spec in H0.
    destruct H0.
    rewrite H0.
    auto.
    apply vert_prop.Dec.F.empty_iff in H0; contradiction.
    unfold IndependentSet.
    intros.
    intros Hnot.
    rewrite Vertices.add_spec in H0,H1.
    destruct H0.
    destruct H1.
    rewrite H0 in Hnot.
    rewrite H1 in Hnot.
    apply IsEdgeEnum in Hnot.
    apply edges_irreflexive in Hnot.
    auto.
    apply vert_prop.Dec.F.empty_iff in H1; contradiction.
    apply vert_prop.Dec.F.empty_iff in H0; contradiction.
  Qed.



  (* Definition of a Maximal Independent Set with respect to a graph *)
  Inductive MaximalIndSet (X : Vertices.t) (G : t) : Prop :=
  | defMaximalIndSet :
      IndSet X G ->
      (forall x, IndSet (Vertices.add x X) G -> Vertices.In x X) ->
      MaximalIndSet X G.
  
  (* An equivalent definition *) 
  Inductive MaximalIndSet_contrapos
  (X : Vertices.t) (G : t) : Prop :=
  | defMaximalIndSet_contrapos :
      IndSet X G ->
      (forall x, ~ Vertices.In x X -> ~ IndSet (Vertices.add x X) G) ->
      MaximalIndSet_contrapos X G.

  Definition maximalindset (X : Vertices.t) (G : t) : Prop :=
    IndSet X G -> forall x, IsVertex x G -> Vertices.In x X \/ ~IndSet (Vertices.add x X) G.

  Lemma idk : forall X G, {IndSet X G} + {~IndSet X G}.
  Proof.
    intros.
    Admitted.

  Lemma Maximal_eq : forall X G, MaximalIndSet X G <-> maximalindset X G.
  Proof.
    unfold maximalindset.
    split; intros; auto.
    inversion H.
    Admitted.

  Theorem MaximalIndSet_eq : forall X G, MaximalIndSet X G <-> MaximalIndSet_contrapos X G.
  Proof.
    split; intros H; constructor; inversion H; try intros x; auto.
    destruct (vert_prop.In_dec x) with (s := X); auto.
    apply H1 in n.
    contradiction.
  Qed.

  (* Makes a maximal independent set by adding all vertices of a graph
     to a set if adding them results in an independent set. *)
  Fixpoint Mk_aux (s : list Vertices.E.t) (X : Vertices.t)
           (g : t) : Vertices.t :=
    match s with
    | nil => X
    | cons h t => if indSet (Vertices.add h (Mk_aux t X g)) g
                  then (Vertices.add h (Mk_aux t X g)) else Mk_aux t X g
    end.

  
  (* Calls Mk_aux with some set.  Maybe it would be nice to enforce that
     X is an IndSet 
   *)
  Definition MkMaximalIndSet (X : Vertices.t) (G : t)
    : Vertices.t :=
    Mk_aux (Vertices.elements (enumVertices G)) X  G.


  (* This seems like it should be an equivalent function *)
  Definition MkMaximalIndSet' (X : Vertices.t) (G : t)
    : Vertices.t :=
    Vertices.fold (fun x X' =>
                     if indSet (Vertices.add x X') G 
                                 then
                       (Vertices.add x X') else X') (enumVertices G) X.
  
  (* Some Specs about MkMaximalIndSet Start here *)
  Theorem MkMaximalIndSet_spec : forall X G,
      IndSet X G -> IndSet (MkMaximalIndSet X G) G.
  Proof.
    intros X G H.
    unfold MkMaximalIndSet.
    induction ((Vertices.elements (enumVertices G))); auto.
    simpl.
    destruct (indSet (Vertices.add a (Mk_aux l X G)) G) eqn:H3;
      try apply indSet_true_iff in H3;
    auto.
  Qed.
  
  Theorem MkMaximalIndSet'_spec : forall X G,
      IndSet X G -> IndSet (MkMaximalIndSet' X G) G.
  Proof.
    intros X G H.
    unfold MkMaximalIndSet'.
    apply DG_Facts.VertProperties.P.fold_rec_weak; intros; auto.
        destruct (indSet (Vertices.add x a) G) eqn:H4;
      try apply indSet_true_iff in H4;
      auto.
  Qed.
  
  (* Might need more stuff for this and it might not even be useful *)
  Lemma MaximalIndSet_spec : forall X G x,
      let X' := (MkMaximalIndSet X G) in ~IndSet (Vertices.add x X') G \/ Vertices.In x X.
  Proof.
  Admitted.
  
  (* Just leaving this here if I end up needing something else or think 
     of anything *) 

  (* I'm hoping this turns out to hold *) 
  Lemma IndSet_add_spec : forall x X G,
      IndSet (Vertices.add x (Mk_aux nil X G)) G ->
      Vertices.In x X \/ ~ IndSet (Vertices.add x (Mk_aux nil X G)) G.
  Proof.
    intros.
    right.
  Admitted.

  Lemma Mk_aux_spec : forall x a l X G, 
   Vertices.In x (Mk_aux l X G) <-> Vertices.In x (Mk_aux (a :: l) X G).
  Proof.
    split;
    intros;
      simpl in *;
      destruct (indSet (Vertices.add a (Mk_aux l X G)) G) eqn:H1; auto;
        try rewrite H1 in H;
        try apply Vertices.add_spec;
        try apply Vertices.add_spec in H;
        auto.
    destruct H.
    apply indSet_true_iff in H1.
    assert (IndSet (Vertices.add a (Mk_aux l X G)) G) by auto.
    apply IndSet_add_spec in H1.
    destruct H1; auto.
    rewrite <- H in H1.
    auto.
    unfold not in H1.
    apply H1 in H0; destruct H0.
    auto.
  Qed.

  (* This is used in the next proof and seems reasonable *)
  Lemma Mk_aux_spec1 : forall x a l X G,
      IndSet (Vertices.add x (Mk_aux (a :: l) X G)) G ->
      IndSet (Vertices.add x (Mk_aux l X G)) G.
    Proof.
      intros.
      simpl in *.
      destruct (indSet (Vertices.add a (Mk_aux l X G)) G) eqn:H1; auto.
    Admitted.
    
    (* MkMaximalIndSet actually makes a Maximal Independent Set *)
    Theorem MkMaximalIndSet_spec2 : forall X G,
        IndSet X G-> MaximalIndSet (MkMaximalIndSet X G) G.
    Proof.
      intros.
      constructor.
      apply MkMaximalIndSet_spec.
      auto.
      intros.
      unfold MkMaximalIndSet in *.
      induction (Vertices.elements (enumVertices G)).
      simpl.
      assert (IndSet (Vertices.add x (Mk_aux nil X G)) G) by auto.
      apply IndSet_add_spec in H0.
      destruct H0; auto; try contradiction.
      apply Mk_aux_spec.
      apply IHl.
      apply Mk_aux_spec1 in H0.
      auto.
    Qed.
  
  Lemma MkMaximalIndSet_spec3 : forall (x : Vertices.E.t) (X : Vertices.t)  (G : t),
      True.
    Proof.
    Admitted.

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


Inductive mkCS : vertex -> t -> list (list nat) -> list (list nat) -> Prop :=
| mkCS_nilnil :
    forall G l,
      O = lV G -> 
      mkCS O G l (nil::nil)
| mkCS_Sxnil :
    forall G x,
      S x = lV G -> 
      mkCS (S x) G nil nil
| mkCS_indep :
    forall G x cand Lin Lout,
      S x = lV G -> 
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = true ->
      mkCS (S x) G (cand :: Lin) ((x :: cand) :: Lout)
| mkCS_nindep1 :
    forall G x cand Lin Lout,
      S x = lV G ->       
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = false ->
      LFMIS G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand) ->
      LFMIS (LiftGraph x G) (rmvNeighbors x G cand) cand ->
      mkCS (S x) G (cand :: Lin) ((x :: rmvNeighbors x G cand) :: cand :: Lout)
| mkCS_nindep2 :
    forall G x cand Lin Lout,
      S x = lV G -> 
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = false ->
      LFMIS G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand) ->
      ~LFMIS (LiftGraph x G) (rmvNeighbors x G cand) cand ->
      mkCS (S x) G (cand :: Lin) (cand :: Lout)
| mkCS_nindep3 :
    forall G x cand Lin Lout,
      S x = lV G ->       
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = false ->
      ~LFMIS G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand) ->
      mkCS (S x) G (cand :: Lin) (cand :: Lout).


                                                                                                                     
(* Fixpoint mkCandidateSets (G : t) (l : list (Vertices.t)) :  list Vertices.t :=  *)
(*   match lV G with *)
(*   | O => nil::nil *)
(*   | S V' => *)
(*     match l with *)
(*     | nil => nil *)
(*     | cons cand l' => *)
(*         if independent_lGraph G (V' :: cand) then (V' :: cand) :: mkCandidateSets G l' *)
(*         else if isMIS G (V' :: rmvNeighbors V' G cand) *)
(*              then if LFMIS_dec (LiftGraph V' G) (rmvNeighbors V' G cand) cand *)
(*                   then (V' :: rmvNeighbors V' G cand) :: cand :: mkCandidateSets G l' *)
(*                   else cand :: mkCandidateSets G l' *)
(*              else cand :: mkCandidateSets G l' *)
(*     end *)
(*   end. *)
