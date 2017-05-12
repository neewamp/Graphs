(*
  This module implements the most general
  form of our graphs. These unidrected
  graphs satisfy the following properties :

  (** Fill these in **)
  (* How do we ensure our graphs are simple? *)

*)

(* Things we need:
    - Ordering over sets
    - Interface for directed graphs, undirected graphs, simple graphs,
        hypergraphs.
      - See (http://ocamlgraph.lri.fr/doc/Sig_pack.S.html) for required options

    - Graph implementation needs to support the following interface

*)

Require Import MSets MSetFacts.
Module Type DirectedGraphs.

  Declare Module Edges : Sets.
  (* the type of a vertex *)
  Declare Module Vertices : Sets.
  Notation vertex := Vertices.elt. (* Vertices.E.t *)
  
  (* The type of an edge *)
  Notation edge := Edges.elt.

  (* (Potentially) Extensional (In)Equality over edges/vertices *)
  Notation "V1 =V= V2" := (Vertices.eq V1 V2) (at level 60).
  Notation "V1 <V> V2" := (~ Vertices.eq V1 V2) (at level 60). 
  Notation "E1 =E= E2" := (Edges.eq E1 E2) (at level 60).
  Notation "E1 <E> E2" := (~ Edges.eq E1 E2) (at level 60). 
  Notation "v1 =v= v2" := (Vertices.E.eq v1 v2) (at level 60).
  Notation "v1 <v> v2" := (~ Vertices.E.eq v1 v2) (at level 60). 
  Notation "e1 =e= e2" := (Edges.E.eq e1 e2) (at level 60).
  Notation "e1 <e> e2" := (~ Edges.E.eq e1 e2) (at level 60). 
  (** Basic elements **)
    (* The type of graphs *)
  Parameter t : Type.
    (* the empty graph *)
  Parameter empty : t.  
  Parameter buildEdge : vertex -> vertex -> edge.
  Parameter destructEdge : edge -> vertex * vertex %type.

  Parameter destructEdge_spec1 : forall (e1 e2 : edge),
      e1 =e= e2 -> fst (destructEdge e1) =v= fst (destructEdge e2).
  
  Parameter destructEdge_spec2 : forall (e1 e2 : edge),
      e1 =e= e2 -> snd (destructEdge e1) =v= snd (destructEdge e2).

  Parameter buildEdge_spec : forall v1 v2 v3 v4,
      v1 =v= v2 -> v3 =v= v4 -> buildEdge v1 v3 =e= buildEdge v2 v4.
  
  (*
  Parameter src : edge -> vertex.
  Parameter snk : edge -> vertex.
  *)

  (** Membership Predicates and functions **)
  Parameter IsEmpty : t -> Prop.
  Parameter IsVertex : vertex -> t -> Prop.
  Parameter IsEdge : edge -> t -> Prop.
  
  Parameter isEmpty : t -> bool.
  Parameter isVertex : vertex -> t -> bool.
  Parameter isEdge : edge -> t -> bool.

  Parameter IsEmpty_reflect : forall G, reflect (IsEmpty G) (isEmpty G).
  Parameter IsVertex_reflect : forall G v, reflect (IsVertex v G) (isVertex v G).
  Parameter IsEdge_reflect : forall G e, reflect (IsEdge e G) (isEdge e G).

  (* t here is the tyoe of graphs, X.t is the base type delcared in X*)
  Parameter enumVertices : t -> Vertices.t.
  Parameter enumEdges : t -> Edges.t.

  (** Construction Restrictions **)
  Parameter Empty : IsEmpty empty.
  Parameter Empty_vertices :
    forall G, IsEmpty G -> (Vertices.Empty (enumVertices G)).
  Parameter Empty_edges :
    forall G, IsEmpty G -> (Edges.Empty (enumEdges G)).
  Parameter IsVertexEnum :
    forall G v, IsVertex v G <-> Vertices.In v (enumVertices G).
  Parameter IsEdgeEnum :
    forall G e, IsEdge e G <-> Edges.In e (enumEdges G). 
  Parameter Edge_exists1 :
    forall G e, IsEdge e G -> IsVertex (fst (destructEdge e)) G.
  Parameter Edge_exists2 :
    forall G e, IsEdge e G -> IsVertex (snd (destructEdge e)) G.
  
  (** Elementary Graph Operations **)
  Parameter addVertex : vertex -> t -> t.
  Parameter addEdge : edge -> t -> t.
  Parameter removeVertex : vertex -> t -> t. 
  Parameter removeEdge : edge -> t -> t.

  (** Specifications of these graph operations **)
  Parameter addVertex_spec1 :
    forall G v, IsVertex v (addVertex v G).
  Parameter addVertex_spec2 :
    forall G v1 v2, v1 <v> v2 ->
      IsVertex v1 G <-> IsVertex v1 (addVertex v2 G).
  Parameter addVertex_spec3 :
    forall G v e,
      IsEdge e G <-> IsEdge e (addVertex v G).

  Parameter addEdge_spec1 :
    forall G e,
      IsVertex (fst (destructEdge e)) G->
      IsVertex (snd (destructEdge e)) G->
         IsEdge e (addEdge e G).
  Parameter addEdge_spec2 :
     forall G e1 e2, e1 <e> e2 ->
       IsEdge e1 G <-> IsEdge e1 (addEdge e2 G).
  Parameter addEdge_spec3 : forall G v e,
    IsVertex v G <-> IsVertex v  (addEdge e G).

  Parameter removeVertex_spec1 :
    forall G v, ~ IsVertex v (removeVertex v G).
  Parameter removeVertex_spec2 :
    forall G v1 v2, v1 <v> v2 ->
      IsVertex v1 G <-> IsVertex v1 (removeVertex v2 G).
  Parameter removeVertex_spec3 :
    forall G v e,
      IsEdge e (removeVertex v G) <->
      IsEdge e G /\
        (fst (destructEdge e)) <v> v /\
        (snd (destructEdge e)) <v> v.
  Parameter removeVertex_spec4 :
    forall G v e,
      IsEdge e G ->
        (fst (destructEdge e) =v= v) \/
        (snd (destructEdge e) =v= v) ->
          ~ IsEdge e (removeVertex v G).

  Parameter removeEdge_spec1 :
    forall G e, ~ IsEdge e (removeEdge e G).
  Parameter removeEdge_spec2 :
    forall G e1 e2, e1 <e> e2 -> 
      IsEdge e1 G <-> IsEdge e1 (removeEdge e2 G).
  Parameter removeEdge_spec3 :
    forall G v e,
      IsVertex v G <-> IsVertex v (removeEdge e G).

End DirectedGraphs.