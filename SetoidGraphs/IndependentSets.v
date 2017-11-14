Require Import GraphInterface
        MathClasses.interfaces.finite_sets
        MathClasses.theory.finite_sets.
Require Import MathClasses.implementations.list_finite_set
        MathClasses.orders.lattices
        MathClasses.orders.orders.
Require Import MathClasses.interfaces.abstract_algebra.
(*         MathClasses.interfaces.orders. *)
Section IndependentSets.
  Context `(GraphProperties).

  Program  Definition IndependentSet (X : set_type vertex) (g : t) :=
    forall (x y : vertex),
      contains x X -> contains y X ->
      ~contains (buildEdge x y) (enumEdges g).

  Context `(listset vertex).
  Definition asdf : Type.
  
Definition independentSet (X : set_type vertex) (g : t)
    :=
      fset_map id X.
  
  Definition ValidSet (X : set_type vertex) (G : t) :=
    forall (x : vertex) , contains x X -> contains x (enumVertices G).

  Theorem validSetRecr : 
    forall x (X : set_type vertex) G,
      ValidSet (join x X) G -> ValidSet X G.
  Proof.
    red. intros.
    unfold ValidSet in *.
    apply H4; auto.
    rewrite fset_in_join.
    auto.
  Qed.
