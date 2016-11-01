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
  Notation vertex := Vertices.elt.
  
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
  Parameter t : Set.
    (* the empty graph *)
  Parameter empty : t.  
  Parameter buildEdge : vertex -> vertex -> edge.
  Parameter destructEdge : edge -> (vertex*vertex)%type.
  
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

  Parameter enumVertices : t -> Vertices.t.
  Parameter enumEdges : t -> Edges.t.

  (** Construction Restrictions **)
  Parameter Empty : IsEmpty empty.
  Parameter Empty_vertices :
    forall G, IsEmpty G -> (Vertices.Empty (enumVertices G)).
  Parameter Empty_edges :
    forall G, IsEmpty G -> (Vertices.Empty (enumVertices G)).
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

Require Import MSetAVL.

Module myGraph : DirectedGraphs.
  


  Module pos :=  PositiveOrderedTypeBits.
  
  Module Vertices := MSetAVL.Make pos.
  Definition node := pos.t.
  Module Edge := PairOrderedType pos pos.
  Module Edges := MSetAVL.Make Edge.


  Module vert_facts := WFacts (Vertices).
  Module edge_facts := WFacts (Edges).
  Module vert_prop := WProperties (Vertices).
  Module edge_prop := WProperties (Edges).



  Definition edge := Edges.t.
  Definition v_set := Vertices.t.
  Definition e_set := Edges.t.
  Record Graph :=
    mkgraph {
        V : v_set;
        E : e_set;
      }.

  Definition t := Graph.

  Definition empty := mkgraph Vertices.empty Edges.empty.
  Open Scope positive_scope.

  Notation vertex := Vertices.elt.
    

  Definition buildEdge (n n1 : vertex): Edges.elt :=
    (n,n1).


  (* Definition destructEdge : edge -> (vertex * vertex) := *)
  (*   fun X : edge => let (p, p0) := X in buildEdge p p0. *)




  Definition buildPair : vertex -> vertex -> vertex * vertex :=
    fun x y => (x,y).

  
Definition destructEdge : Edge.t -> (vertex * vertex) :=
  fun X : Edge.t => let (p, p0) := X in (p, p0).

  (* intros. *)
  (* destruct X. *)
  (* exact (p, p0). *)
(*Defined.*)



  Definition isemptyP : v_set -> e_set -> Prop :=
    fun (x : v_set) (y : e_set) => Vertices.Empty x  /\ Edges.Empty y.



  Definition  IsEmpty : Graph -> Prop :=
    fun X : Graph =>
      match X with
      | {| V := V0; E := e0 |} => Vertices.Empty V0  /\ Edges.Empty e0
      end.

  Definition IsVertex : Vertices.elt -> Graph -> Prop :=
    fun (n : Vertices.elt) (g : Graph)  =>
      match g with
      | {| V:= v; E := e0 |} => Vertices.In n v
      end.

  Definition IsEdge : Edges.elt -> Graph -> Prop :=
    fun (e : Edges.elt) (g : Graph) =>
      match g with
      | {| V := v; E := e0 |} => Edges.In e e0
      end.
  
    Definition isEmpty : Graph -> bool :=
      fun (g : Graph) =>
        match g with
        | {| V := v; E := e |} =>
          andb (Vertices.is_empty v) (Edges.is_empty e)
        end.

    Definition isVertex : Vertices.elt -> Graph -> bool :=
      fun (n : Vertices.elt) (g : Graph)  =>
        match g with
        | {| V:= v; E := e0 |} => Vertices.mem n v
        end.

    Definition isEdge : Edges.elt -> Graph -> bool :=
      fun (e : Edges.elt) (g : Graph) =>
        match g with
        | {| V := v; E := e0 |} => Edges.mem e e0
        end.

    Lemma IsEmpty_reflect :
      forall G : Graph, reflect (IsEmpty G) (isEmpty G).
    Proof.
      intros.
      unfold IsEmpty.
      unfold isEmpty.
      destruct G.
      apply iff_reflect.
      rewrite <- Vertices.is_empty_spec.
      rewrite <- Edges.is_empty_spec.
      split; intros; try apply andb_true_iff; auto.
    Qed.


    Lemma IsVertex_reflect :
      forall (G : Graph) (v : node),
        reflect (IsVertex v G) (isVertex v G).
    Proof.
      intros.
      destruct G.
      simpl.
      apply iff_reflect.
      split; intros; try apply Vertices.mem_spec; auto.
    Qed.

    Lemma IsEdge_reflect :
     forall (G : Graph) (e : Edges.elt), reflect (IsEdge e G) (isEdge e G).
    Proof.
      intros.
      destruct G.
      apply iff_reflect.
      unfold IsEdge, isEdge.
      split; try apply Edges.mem_spec; auto.
    Qed.
    
    Definition enumVertices : Graph -> Vertices.t :=
      fun (g : Graph) =>
        match g with
        | {| V := v; E := e |} =>  v
        end.
    
    Definition enumEdges : Graph -> Edges.t :=
      fun (g : Graph) =>
        match g with
        | {| V := v; E := e |} => e
        end.
    
    Lemma Empty : IsEmpty empty.
    Proof.
      unfold empty.
      unfold IsEmpty.
      split.
      apply Vertices.empty_spec.
      apply Edges.empty_spec.
    Qed.
      
    Lemma Empty_vertices :
      forall G : Graph, IsEmpty G -> Vertices.Empty (enumVertices G).
    Proof.
      intros.
      destruct G.
      simpl in *.
      destruct H.
      auto.
    Qed.
      
    Lemma Empty_edges :
     forall G : t, IsEmpty G -> Vertices.Empty (enumVertices G).
    Proof.
      intros [V E] H. simpl in *; destruct H.
      auto.
    Qed.

    Lemma IsVertexEnum :
     forall (G : t) (v : Vertices.elt), IsVertex v G <-> Vertices.In v (enumVertices G).
    Proof.
      intros [V E] v; split; simpl; intros; auto.
    Qed.
    Lemma IsEdgeEnum :
     forall (G : t) (e : Edges.elt), IsEdge e G <-> Edges.In e (enumEdges G).
    Proof.
      intros [V E] v; split; simpl; intros; auto.
    Qed.


    Lemma Edge_exists1 :
     forall (G : t) (e : Edges.elt),
     IsEdge e G -> IsVertex (fst (destructEdge e)) G.
    Proof.
      intros [V E] e H.
      simpl in *.
      unfold destructEdge.
      destruct e.
      simpl.
      Admitted.
      



End myGraph.  
  




(*   Parameter buildEdge : elt -> elt -> elt.*)
   Parameter destructEdge : elt -> elt * elt.
   Parameter IsEmpty : t -> Prop.
   Parameter IsVertex : elt -> t -> Prop.
   Parameter IsEdge : elt -> t -> Prop.
   Parameter isEmpty : t -> bool.
   Parameter isVertex : elt -> t -> bool.
   Parameter isEdge : elt -> t -> bool.
   Parameter IsEmpty_reflect :
     forall G : t, reflect (IsEmpty G) (isEmpty G).
   Parameter IsVertex_reflect :
     forall (G : elt) (v : t), reflect (IsVertex G v) (isVertex G v).
   Parameter IsEdge_reflect :
     forall (G : elt) (e : t), reflect (IsEdge G e) (isEdge G e).
   Parameter enumVertices : t -> t.
   Parameter enumEdges : t -> t.
   Parameter Empty : IsEmpty empty.
   Parameter Empty_vertices :
     forall G : t, IsEmpty G -> Empty (enumVertices G).
   Parameter Empty_edges :
     forall G : t, IsEmpty G -> Empty (enumVertices G).
   Parameter IsVertexEnum :
     forall (G : t) (v : elt), IsVertex v G <-> In v (enumVertices G).
   Parameter IsEdgeEnum :
     forall (G : t) (e : elt), IsEdge e G <-> In e (enumEdges G).
   Parameter Edge_exists1 :
     forall (G : t) (e : elt),
     IsEdge e G -> IsVertex (fst (destructEdge e)) G.
   Parameter Edge_exists2 :
     forall (G : t) (e : elt),
     IsEdge e G -> IsVertex (snd (destructEdge e)) G.
   Parameter addVertex : elt -> t -> t.
   Parameter addEdge : elt -> t -> t.
   Parameter removeVertex : elt -> t -> t.
   Parameter removeEdge : elt -> t -> t.
   Parameter addVertex_spec1 :
     forall (G : t) (v : elt), IsVertex v (addVertex v G).
   Parameter addVertex_spec2 :
     forall G v1 v2 : t,
     ~ eq v1 v2 -> IsVertex v1 G <-> IsVertex v1 (addVertex v2 G).
   Parameter addVertex_spec3 :
     forall (G : t) (v e : elt),
     IsEdge e G <-> IsEdge e (addVertex v G).
   Parameter addEdge_spec1 :
     forall (G : t) (e : elt),
     IsVertex (fst (destructEdge e)) G ->
     IsVertex (snd (destructEdge e)) G -> IsEdge e (addEdge e G).
   Parameter addEdge_spec2 :
     forall G e1 e2 : t,
     ~ eq e1 e2 -> IsEdge e1 G <-> IsEdge e1 (addEdge e2 G).
   Parameter addEdge_spec3 :
     forall (G : t) (v e : elt),
     IsVertex v G <-> IsVertex v (addEdge e G).
   Parameter removeVertex_spec1 :
     forall (G : t) (v : elt), ~ IsVertex v (removeVertex v G).
   Parameter removeVertex_spec2 :
     forall G v1 v2 : t,
     ~ eq v1 v2 -> IsVertex v1 G <-> IsVertex v1 (removeVertex v2 G).
   Parameter removeVertex_spec3 :
     forall (G : t) (v e : elt),
     IsEdge e (removeVertex v G) <->
     IsEdge e G /\
     ~ eq (fst (destructEdge e)) v /\ ~ eq (snd (destructEdge e)) v.
   Parameter removeVertex_spec4 :
     forall (G v : t) (e : elt),
     IsEdge e G ->
     eq (fst (destructEdge e)) v \/ eq (snd (destructEdge e)) v ->
     ~ IsEdge e (removeVertex v G).
   Parameter removeEdge_spec1 :
     forall (G : t) (e : elt), ~ IsEdge e (removeEdge e G).
   Parameter removeEdge_spec2 :
     forall G e1 e2 : t,
     ~ eq e1 e2 -> IsEdge e1 G <-> IsEdge e1 (removeEdge e2 G).
   Parameter removeEdge_spec3 :
     forall (G : t) (v e : elt),
     IsVertex v G <-> IsVertex v (removeEdge e G).
 End
