Set Implicit Arguments.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.
Require Import String.

Require Import DirectedGraphs DirectedGraphs_morph maxind.

Definition Comp (state A ERR : Type) := state -> (state * A) + ERR.

Section Comp.
  Variables state A ERR : Type.

  Definition bind (B : Type) (c : Comp state A ERR) (f : A -> Comp state B ERR)
    : Comp state B ERR :=
    fun s =>
      match c s with
      | inl (s', a) => f a s'
      | inr err => inr err
      end.

  Definition ret (a : A) : Comp state A ERR := fun s => inl (s, a).

  Definition get : Comp state state ERR :=
    fun s => inl (s, s).

  Definition upd (f : state -> state) : Comp state unit ERR :=
    fun s => inl (f s, tt).

  Definition raise (err : ERR) : Comp state A ERR := fun _ => inr err.

  Definition trycatch
             (c : Comp state A ERR)
             (d : Comp state A ERR)
    : Comp state A ERR :=
    fun s =>
      match c s with
      | inl p => inl p
      | inr _ => d s
      end.
End Comp.

Arguments bind [_ _ _ _] _ _ _.
Arguments ret [_ _ _] _ _.
Arguments get [_ _] _.
Arguments upd [_ _] _ _.
Arguments raise [_ _ _] _ _.
Arguments trycatch [_ _ _] _ _ _.

Notation "x <- c ; f" := (bind c (fun x => f)) (at level 50).
Notation "c ;; d" := (bind c (fun _ => d)) (at level 50).

Notation "'try' c 'with' d" := (trycatch c d) (at level 49).

Fixpoint mapM (state A B ERR : Type) (f : A -> Comp state B ERR) (l : list A)
  : Comp state (list B) ERR :=
  match l with
  | nil => ret nil
  | a :: l' =>
    bind (f a) (fun b =>
    bind (mapM f l') (fun l => ret (b :: l)))
  end.

Module Lawler (G : DirectedGraphs) (X : MAX_IND_SETS G).
  Module GraphExtras := DirectedGraphMorph G.
  Import GraphExtras.

  Module VertexSet <: OrderedType.OrderedType. (*for compat with FMaps*)
    Definition t := G.Vertices.t.
    Definition eq := G.Vertices.eq.
    Definition lt := G.Vertices.lt.
    Lemma eq_refl : forall x : t, eq x x.
    Proof. intros s y; split; auto. Qed.
    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. intros s t H x; rewrite H; split; auto. Qed.
    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros x y z H H1 a; rewrite H, H1; split; auto. Qed.
    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
      intros x y z H H1.
      destruct G.Vertices.lt_strorder as [X Y].
      apply (Y x y z); auto.
    Qed.      
    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      intros x y H Hcontra.
      destruct G.Vertices.lt_strorder as [X Y].              
      destruct (G.Vertices.compare_spec x y).
      { rewrite H0 in H; apply (X _ H). }
      { rewrite Hcontra in H0; apply (X _ H0). }
      rewrite Hcontra in H0; apply (X _ H0).      
    Qed.      
    Lemma compare : forall x y : t, Compare lt eq x y.
    Proof. Admitted. (*Does the Sets interface even export decidability of lt?*)
    Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    Proof. apply G.Vertices.eq_dec. Qed.
  End VertexSet.
    
  Module M := Make VertexSet. (*map from VertexSet -> ?A*)
  Module MFacts := Facts M.
  Module MProps := Properties M.

  Definition D := M.t positive. (*map from VertexSet -> positive*)

  Definition induced_subgraph (g : G.t) (s : VertexSet.t) : G.t :=
    G.Vertices.fold G.removeVertex s g.

  Definition LawlerComp := Comp D positive string.
  
  Section Lawler.    
    Variable g : G.t.

    Local Open Scope string_scope.    

    Definition min (l : list positive) := List.fold_left Pos.min l 1%positive.
    
    Definition get_chromatic_number (s : VertexSet.t) : LawlerComp :=
      bind 
        (@get _ _)
        (fun d : D =>
           match M.find s d with
           | None => raise "Table lookup failed"
           | Some p => ret p
           end).

    Require Import Coq.Program.Wf.    
    Program Fixpoint Lawler
            (s : VertexSet.t)
            {measure (G.Vertices.cardinal s)}
      : LawlerComp :=
      try get_chromatic_number s
      with
        if X.max_ind_set s g then
          let chi := 1%positive in 
          upd (M.add s chi);; ret chi
        else
          let gs := induced_subgraph g s in
          l <- mapM (fun s' => @Lawler (G.Vertices.diff s s') _) (X.max_ind_sets gs);
          let chi := (min l + 1)%positive in 
          upd (M.add s chi);;
          ret chi.
    Next Obligation. Admitted. (*TODO: need "cardinal MIS > 0"*)
  End Lawler.
End Lawler.
