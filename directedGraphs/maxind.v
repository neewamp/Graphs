Require Import Structures.Orders NArith MSetInterface.

Require Import DirectedGraphs DirectedGraphs_morph.

Module Type MAX_IND_SETS (G : DirectedGraphs).
  Module VertexSet <: MSetInterface.Sets := G.Vertices.
  
  (** List the maximal independent sets g. *)
  Parameter max_ind_sets : forall (g : G.t), list VertexSet.t.

  (** Check whether s is an independent set in g. *)
  Parameter ind_set : forall (s : VertexSet.t) (g : G.t), bool.

  (** [s] is an independent set in G *)
  Definition IndSet (s : VertexSet.t) (g : G.t) : Prop :=
    VertexSet.For_all (fun x =>
      VertexSet.For_all (fun y => 
        VertexSet.E.eq x y \/
        ~G.IsEdge (G.buildEdge x y) g) s) s.

  Definition MaxIndSet (s : VertexSet.t) (g : G.t) : Prop :=
    IndSet s g /\
    VertexSet.For_all (fun x =>
      VertexSet.In x s \/ 
      ~IndSet (VertexSet.add x s) g) (G.enumVertices g).

  Parameter max_ind_sets_ok :
    forall g, List.Forall (fun s => MaxIndSet s g) (max_ind_sets g).

  Parameter ind_set_ok :
    forall g s, reflect (IndSet s g) (ind_set s g).
End MAX_IND_SETS.  