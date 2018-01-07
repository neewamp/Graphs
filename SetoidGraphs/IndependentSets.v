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

(* Ltac normG := *)
(*   match goal with *)
(*   | H : ?T |- _ => *)
Class ValidSetType `(SG : SimpleUndirectedGraph)
  : Type :=
  {
    ValidSet : set_type vertex -> t -> Prop;
    ValidSet_spec : forall X g,
        ValidSet X g <-> 
        forall  x : vertex, x ∈ X → x ∈ enumVertices g
  }.

Section ValidSet.
  Context `(SG : SimpleUndirectedGraph).
  
  Program Instance validset : ValidSetType SG :=
    Build_ValidSetType SG
      (fun (X : set_type vertex) (g : t) =>
         forall  x : vertex, x ∈ X → x ∈ enumVertices g)
      _.
  Next Obligation.
    split; intros; auto.
  Defined.
  
End ValidSet.  

Class IndependentType `(SG : SimpleUndirectedGraph)
  : Type :=
  {
    IndependentSet : set_type vertex -> t -> Prop;
    IndependentSet_spec :
      forall (X : set_type vertex) (g : t),
        IndependentSet X g <-> 
      forall (x y : vertex),
        contains x X -> contains y X ->
        ~contains (buildEdge x y) (enumEdges g)
  }.
(* Problems *)    

Class IndSetType
      `(SG : SimpleUndirectedGraph)
      (Valid : ValidSetType SG)
      (Ind : IndependentType SG)
      (IndSet : set_type vertex -> t -> Prop)
      (IndSet_spec1 :
        forall X g,
          IndSet X g -> ValidSet X g)
      (IndSet_spec2 :
        forall X g,
          IndSet X g ->
          IndependentSet X g)
      (IndSet_spec3 :
        forall X g, IndSet X g <->
                    (IndependentSet X g)/\ (ValidSet X g))
  := {}.

Section IndependentSets.
  Context `(Ind : IndSetType).

  (* Definition IndependentSet (X : set_type vertex) (g : t) := *)
  (*   forall (x y : vertex), *)
  (*     contains x X -> contains y X -> *)
  (*     ~contains (buildEdge x y) (enumEdges g). *)


  (* Context `(listset vertex). *)
  (* Definition asdf : Type. *)
  
  Definition independentSet (X : set_type vertex) (G : t)
    := for_all (fun v1 => for_all
        (fun v2 => negb (mem (buildEdge v1 v2) (enumEdges G))) X) X.
  
  Definition validSet (X : set_type vertex) (G : t) : bool :=
    for_all (fun  x => if mem x X then mem x (enumVertices G) 
            else true ) X.

  Definition indSet (X : set_type vertex) (G : t) : bool :=
    validSet X G && independentSet X G.

  Ltac unfoldInd :=
    unfold independentSet in *;
    unfold validSet in *;
    unfold indSet in *.
  
  Ltac Split :=
    match goal with
    | [ |- context[?A <-> ?B]] => split; intros
    end.
  Ltac Reflect :=
    match goal with
    | [ |- context[reflect ?A ?B]] => apply iff_reflect
    end.

  Ltac For_allNorm H :=
    match H with
    | forall v, v ∈ ?V -> ?B =>
          let rec search n :=
          (match n with
          | S (S (?n)) => 
            (match goal with
             | [H1 : ?v ∈ V |- _] =>
               let H2 := fresh "H2" in
               assert (H2 : v ∈ V ) by (exact H1);
               apply H in H2; (search (S ?n))
             end)
           end)
      in try (search 10)

    end.
        
Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                   clear x; specialize (H x')
         end.

Ltac insterKeep H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU H'.

  (* Ltac imp := *)
  (*   (match goal with *)
  (*    |[ H : forall v : vertex, *)
  (*         v ∈ ?X -> ?B |- _] => *)
  (*     let rec search := *)
  (*         (match goal with *)
  (*          | [H1 : ?v ∈ X |- _] => *)
  (*            insterU H *)
  (*          end) *)
  (*     in search *)
  (*    end). *)

  Ltac normG :=
    intros; unfoldInd;
    match goal with
    | [ |- ~ ?X] => intros Hnot; normG
    | [ |- context[reflect ?A ?B]] =>
      apply iff_reflect; try normG
    | [ |- ?A /\ ?B] => split; try normG
    | [ |- context[?A <-> ?B]] => split; try normG
    | [ |- context[IndependentSet ?X ?G]] => 
      rewrite IndependentSet_spec; intros; try normG
    | [ H : IndependentSet ?X ?G |- _] => 
      rewrite IndependentSet_spec in H; try normG
    | [H : ValidSet ?X ?G |- _] => 
      rewrite ValidSet_spec in H; try normG
    | [ |- ValidSet ?X ?G] => 
      rewrite ValidSet_spec in *; try normG
    | [H : IndSet ?X ?G |- _] => 
      rewrite IndSet_spec3 in H; try normG
    | [ |- IndSet ?X ?G] => 
      rewrite IndSet_spec3 in *; try normG

    | [ H : context[for_all ?f ?V ≡ true] |- _] =>
      rewrite for_all_forall in H; try normG
    | [ |- context[for_all ?f ?V ≡ true] ] =>
      rewrite for_all_forall; intros; try normG
    | [ H : negb ?B ≡ true |- _] => rewrite negb_true_iff in H; try normG
    | [ |- negb ?B ≡ true] => rewrite negb_true_iff; try normG
    | [ H : context[mem ?A ?B ≡ ?Bool] |- _] =>
      destruct (mem_reflect A B); si; try normG
    | [ |- context[mem ?A ?B ≡ ?Bool] ] =>
      let H1 := fresh "H" in
      destruct (mem_reflect A B) eqn:H1; try normG
    end.

  Ltac mem :=
    match goal with
    | [ H : context[mem ?A ?B ≡ ?Bool] |- _] =>
      destruct (mem_reflect A B)
    | [ |- context[mem ?A ?B ≡ ?Bool] ] =>
      let H1 := fresh "H" in
      destruct (mem_reflect A B)
    end.

  Theorem independentSet_reflect :
    forall X G,
  reflect (IndependentSet X G) (independentSet X G). 
  Proof.
    normG.
    {
      mem;
        eauto.
      exfalso.
      intuition.
      eapply H; eauto.
      exfalso.
      apply (H v v0); auto.
    }
    specialize (H x).
    apply H in H0.
    normG.
    apply H0 in H1.
    normG.
  Qed.

  Hint Resolve independentSet_reflect.

  Theorem validSet_reflect :
    forall X G, reflect (ValidSet X G) (validSet X G).
  Proof.
    normG; intros; auto.
    {
      assert (v ∈ X) by auto.
      rewrite mem_iff in H0; auto.
      rewrite H0.
      rewrite <- mem_iff; auto.
    }
    assert (contains x X) by auto.
    apply H in H0.
    rewrite mem_iff in H1; auto.
    rewrite H1 in H0; auto.
    rewrite mem_iff; auto.
  Qed.
  Hint Resolve validSet_reflect.

  Theorem validSetRecr : 
    forall x (X : set_type vertex) G,
      ValidSet (join x X) G -> ValidSet X G.
  Proof.
    normG.
    intros.
    apply H; auto.
    rewrite fset_in_join.
    auto.
  Qed.

  Hint Resolve reflect_iff.
  Hint Resolve iff_reflect.
  Theorem indSet_reflect : forall X G, reflect (IndSet X G) (indSet X G).
  Proof.
    unfoldInd.
    intros.
    apply iff_reflect.
    rewrite andb_true_iff.
    rewrite IndSet_spec3.
    assert (IndependentSet X G <-> independentSet X G ≡ true) by auto.
    assert (ValidSet X G <-> validSet X G ≡ true) by auto.
    rewrite H,H0.
    auto.
    intuition; auto.
  Qed.
  Hint Resolve indSet_reflect.
  Hint Rewrite indSet_reflect.
  Theorem nilIndSet : IndSet ⊥ empty.
  Proof.
    normG;
      try intros x y H; unfold ValidSet; intros;
        try apply fset_notin_empty in H;
        try contradiction.
  Qed.

  (* ⊥ Is bottom *)

  Theorem empty_IndSet_spec : forall G, IndSet ⊥ G.
  Proof.
    intros.
    normG.
    apply fset_notin_empty in H.
    contradiction.
    intros.
    apply fset_notin_empty in H.
    contradiction.
  Qed.

  Lemma bleh : Proper (equiv ==> equiv ==> equiv) buildEdge.
  Proof.
  Admitted.
    
  Global Instance buildEdge_proper :
    Proper ((=) ==> (=) ==> @equiv edge Ae0) buildEdge.
  Proof.
    Admitted.

  Global Instance buildEdge_proper1 :
    Proper (@equiv vertex Ae ==> @equiv vertex Ae ==> @equiv edge Ae0) buildEdge.
  Proof.
    Admitted.

  Print Instances Morphisms.Proper.
(* Set Printing All. *)

Print "=".
  Lemma asd : forall x y , x = y -> (buildEdge x y = buildEdge y x).
    Proof.
      intros.
      (* rewrite H. *)
      Admitted.

  (* buildEdge x0 y ∉ enumEdges G *)
  Theorem nilIndSetAdd : forall x G, contains x (enumVertices G) ->
                       IndSet (join {{x}} bottom) G.
  Proof.
    intros x G H12.
    normG.
    {
      rewrite fset_in_add in H.
      destruct H.
      (* rewrite H. *)
      (* rewrite H; *)
      (*   auto. *)
      (* apply fset_notin_empty in H; contradiction. *)
      admit.
      admit.
    }      
    intros.
    rewrite fset_in_add in H.
    destruct H.
    rewrite H; auto.
    apply fset_notin_empty in H; contradiction.
  Admitted.
  
End IndependentSets.



