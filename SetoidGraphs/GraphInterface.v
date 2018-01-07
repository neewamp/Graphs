Require Import Coq.Setoids.Setoid.
Require Import MathClasses.interfaces.abstract_algebra
        MathClasses.interfaces.finite_sets
        MathClasses.theory.finite_sets
        MathClasses.interfaces.vectorspace
        Bool.

Set Implicit Arguments.

(*
fold f i bot

f (fold f i A) a n b \in A a > b -> fold (A U a) -> 

*)

Class Mem A B := mem: A -> B -> bool.
Class Foldable C :=
  fold : forall {A B : Type} , (A -> B -> B) -> B -> C -> B.

Class DecFullFSet {A}
      `(FS : FullFSet A)
      `(M : Mem A (set_type A))
      `(Fo : Foldable (set_type A))
  : Type :=
  {
    mem_reflect :
      forall (x : A) X, reflect (contains x X) (mem x X)
  }.

Section mem_spec.
  Context `(DecFullFSet A).
  Lemma mem_iff :
    forall (x : A) X, (contains x X) <-> (mem x X) ≡ true.
    intros.
    apply reflect_iff; auto.
    apply mem_reflect.
  Qed.      
End mem_spec.

Section fold_specs.
  Context {A} `(DecFullFSet A).
  Definition for_all (f : A -> bool) (V : set_type A) :=
    fold (fun v acc => f v && acc) true V.
  Parameter for_all_forall : forall f V ,
      for_all f V ≡ true <-> (forall v, contains v V -> f v ≡ true).
End fold_specs.

Class carrier
      `(Vertices : DecFullFSet vertex)
      `(Edges : DecFullFSet edge)
  := {}.

Class Graph
      (t : Type)
      `(car : carrier)
      (enumVertices : t -> set_type vertex)
      (enumEdges : t -> set_type edge)
      (addVertex : vertex -> t -> t)
      (addEdge : edge -> t -> t)
      (removeVertex : vertex -> t -> t)
      (removeEdge : edge -> t -> t)
      (buildEdge : vertex -> vertex -> edge)
      (destructEdge : edge -> vertex * vertex)
      (IsEmpty : t -> Prop)
      (IsVertex : vertex -> t -> Prop)
      (IsEdge : edge -> t -> Prop)
      (isEmpty : t -> bool)
      (isVertex : vertex -> t -> bool)
      (isEdge : edge -> t -> bool)
  : Type := {}.

Class DirectedGraph
      `(Gr : Graph)
      (empty : t)
      (IsEmpty_reflect : forall G:t, reflect (IsEmpty G) (isEmpty G))
      (IsVertex_reflect : forall G v, reflect (IsVertex v G) (isVertex v G))
      (IsVertex_reflect : forall G v, reflect (IsVertex v G) (isVertex v G))
      (IsEdge_reflect : forall G e, reflect (IsEdge e G) (isEdge e G))

  (* t here is the type of graphs, X;t is the base type delcared in X *)


  (* Construction Restrictions *)
      (Empty : IsEmpty empty)

      (IsVertexEnum :
         forall G v, IsVertex v G <-> contains v (enumVertices G))
  (IsEdgeEnum :
     forall G e, IsEdge e G <-> contains e (enumEdges G))
  (Edge_exists1 :
    forall G e, IsEdge e G -> IsVertex (fst (destructEdge e)) G)
  (Edge_exists2 :
    forall G e, IsEdge e G -> IsVertex (snd (destructEdge e)) G)
  
  (* Elementary Graph Operations *)

  (** Specifications of these graph operations **)
  (addVertex_spec1 :
     forall G v, IsVertex v (addVertex v G))
  (addVertex_spec2 :
    forall G v1 v2, Ae v1 v2 ->
                    IsVertex v1 G <-> IsVertex v1 (addVertex v2 G))

  (addVertex_spec3 :
    forall G v e,
      IsEdge e G <-> IsEdge e (addVertex v G))

  (addEdge_spec1 :
    forall G e,
      IsVertex (fst (destructEdge e)) G->
      IsVertex (snd (destructEdge e)) G->
      IsEdge e (addEdge e G))
  (addEdge_spec2 :
     forall G e1 e2, Ae0 e1 e2 ->
                     IsEdge e1 G <-> IsEdge e1 (addEdge e2 G))
  (addEdge_spec3 : forall G v e,
      IsVertex v G <-> IsVertex v (addEdge e G))
  (removeVertex_spec1 :
    forall G v, ~ IsVertex v (removeVertex v G))
  (removeVertex_spec2 :
    forall G v1 v2, ~ Ae v1 v2 ->
      IsVertex v1 G <-> IsVertex v1 (removeVertex v2 G))
  (removeVertex_spec3 :
    forall G v e,
      IsEdge e (removeVertex v G) <->
      IsEdge e G /\
        Ae (fst (destructEdge e)) v /\
        Ae (snd (destructEdge e)) v)
  (removeVertex_spec4 :
    forall G v e,
      IsEdge e G ->
      Ae (fst (destructEdge e)) v \/
      Ae (snd (destructEdge e)) v ->
          ~ IsEdge e (removeVertex v G))
  (removeEdge_spec1 :
    forall G e, ~ IsEdge e (removeEdge e G))
  (removeEdge_spec2 :
    forall G (e1 e2 : edge) , Ae0 e1 e2 ->
      IsEdge e1 G <-> IsEdge e1 (removeEdge e2 G))
  (removeEdge_spec3 :
    forall G v e,
      IsVertex v G <-> IsVertex v (removeEdge e G))
      : Type := {}.

Class SimpleUndirectedGraph 
      `(DG : DirectedGraph)
      {edges_irreflexive : forall (v : vertex) (G : t),
      ~ IsEdge (buildEdge v v) G}
      {undirected : forall (v1 v2 : vertex) (G : t),
          IsEdge (buildEdge v1 v2) G -> IsEdge (buildEdge v2 v1) G}

  : Type := {}.

Section Graphs.
  Context `(Graph).
  Notation "V1 =V= V2" := (conAe V1 V2) (at level 60).
  Notation "V1 <V> V2" := (~ conAe V1 V2) (at level 60). 
  Notation "v1 =v= v2" := (Ae v1 v2) (at level 60).
  Notation "v1 <v> v2" := (~ Ae v1 v2) (at level 60).
  Notation "E1 =E= E2" := (conAe0 E1 E2) (at level 60).
  Notation "E1 <E> E2" := (~ conAe0 E1 E2) (at level 60). 
  Notation "e1 =e= e2" := (Ae0 e1 e2) (at level 60).
  Notation "e1 <e> e2" := (~ Ae0 e1 e2) (at level 60).
End Graphs.


Module GraphProofs.
  Parameter (t : Type).
  Parameter vertex : Type.
  Parameter edge : Type.
  Section f.
    Context `(DecFullFSet vertex).
    Context `(DecFullFSet edge).
    Parameter enumVertices : t -> set_type vertex.
    Parameter enumEdges : t -> set_type edge.
    Parameter addVertex : vertex -> t -> t.
    Parameter addEdge : edge -> t -> t.
    Parameter removeVertex : vertex -> t -> t.
    Parameter removeEdge : edge -> t -> t.
    Parameter buildEdge : vertex -> vertex -> edge.
    Parameter destructEdge : edge -> vertex * vertex.
    Parameter IsEmpty : t -> Prop.
    Parameter IsVertex : vertex -> t -> Prop.
    Parameter IsEdge : edge -> t -> Prop.
    Parameter isEmpty : t -> bool.
    Parameter isVertex : vertex -> t -> bool.
    Parameter isEdge : edge -> t -> bool.
    Parameter ValidSet : set_type vertex -> t -> Prop.
    Parameter ValidSet_spec : forall X g,
        ValidSet X g <-> 
        forall  x : vertex, x ∈ X → x ∈ enumVertices g.

    Parameter IndependentSet : set_type vertex -> t -> Prop.
    Parameter IndependentSet_spec :
      forall (X : set_type vertex) (g : t),
        IndependentSet X g <-> 
      forall (x y : vertex),
        contains x X -> contains y X ->
        ~contains (buildEdge x y) (enumEdges g).

    Parameter IndSet : set_type vertex -> t -> Prop.
    Parameter IndSet_spec1 :
        forall X g,
          IndSet X g -> ValidSet X g.
      (* forall x y, contains x X -> contains y X -> *)
      (*             ~contains (buildEdge x y) (enumEdges g); *)
    Parameter IndSet_spec2 :
        forall X g,
          IndSet X g ->
          IndependentSet X g.
    Parameter IndSet_spec3 :
        forall X g, IndSet X g <->
                    ((IndependentSet X g)/\ (ValidSet X g)).
    Definition independentSet (X : set_type vertex) (G : t)
      := for_all (fun v1 => for_all
        (fun v2 => negb (mem (buildEdge v1 v2) (enumEdges G))) X) X.
    Parameter independentSet_true_iff :
      forall X G,
        reflect (IndependentSet X G) (independentSet X G). 
  End f.
End GraphProofs.
