Require Import MSets MSetFacts PArith DirectedGraphs_morph
        SimpleUndirectedGraphs MSetRBT MSetInterface.
Require Export MaximalIndependentSets SetOrdering.
Set Implicit Arguments.
Set Asymmetric Patterns.

Module AllMIS (DG : SimpleUndirectedGraphs).
  Import DG.
  Module Import maxInd := MaximalIndSets DG.
  Module ordV := OrdProperties Vertices.

  Module Import vOTF := OrderedTypeFacts Vertices.E.

  Module setOrd := SetOrderedType Vertices.

  Module Vert := MSetRBT.Make Nat_as_OT.

  Module misSet := MSetRBT.Make setOrd.
  
  (* I'm going to make a non termination monad based upon 
     cpdt chapter GeneralRec.
     I need to figure out monads anyway
   *)
  CoInductive comp (A : Type) : Type :=
  | Ret : A -> comp A
  | Bnd : forall B, comp B -> (B -> comp A) -> comp A.

  Inductive exec A : comp A -> A -> Prop :=
  | ExecRet : forall x, exec (Ret x) x
  | ExecBnd : forall B (c : comp B) (f : B -> comp A) x1 x2,
      exec (A := B) c x1
      -> exec (f x1) x2
      -> exec (Bnd c f) x2.

  Notation "x <- m1 ; m2" := (Bnd m1 (fun x => m2)) (at level 70).

  CoFixpoint SetLooper (Q : Vert.t) (n : nat) : comp nat :=
    if negb (Vert.is_empty Q) then
      (match Vert.min_elt Q with
       | Some elt => n1 <- (SetLooper (Vert.remove elt Q) (n + 1));
                                    Ret n1
       | None => Ret n
      end)
    else
      Ret n.

  Definition frob A (c : comp A) :=
    match c with
    | Ret x => Ret x
    | Bnd _ c' f => Bnd c' f
    end.

  Lemma exec_frob : forall A (c : comp A) x,
      exec (frob c) x
      -> exec c x.
    destruct c; auto.
  Qed.

  Definition set1 := Vert.add 1 (Vert.add 2 (Vert.empty)).
  
  Lemma tester : exec (SetLooper set1 0)
                      2.
  Proof.
    repeat (apply exec_frob;
    simpl; econstructor).
  Qed.

Section genMis.
  Variable g : DG.t.
  
  Definition ElementsLtEq (j : Vertices.E.t) : Vertices.t :=
    Vertices.fold (fun (v : Vertices.E.t)  S => if ordV.leb v j then
                            Vertices.add v S else
                            S ) Vertices.empty (enumVertices g).

  Definition SubgraphUpTo (j : Vertices.E.t) : DG.t :=
    Vertices.fold (fun v G => if ordV.gtb v j then
                                removeVertex v G else
                                G) (enumVertices g) g.

  Definition neighborhood (v : vertex) (G : t): Vertices.t :=
    Edges.fold (fun edge e =>
                  let fs := (fst (destructEdge edge)) in
                  let sn := (snd (destructEdge edge)) in 
                  if vOTF.eqb v fs
                  then 
                    Vertices.add sn e
                  else 
                    if vOTF.eqb v sn then
                      Vertices.add fs e
                    else
                      e)
               (enumEdges G) (Vertices.add v Vertices.empty).
  
  Definition VertexLtAndAdjacent (j : vertex) (S : Vertices.t)
    : bool :=
    Vertices.exists_ (fun i => if ordV.gtb j i then
                                 isEdge (buildEdge i j) g else
                                 false) S.

  CoFixpoint AllMIS_aux (Q : misSet.t ) (output : list misSet.E.t)
    : comp (list misSet.E.t) :=
    if negb (misSet.is_empty Q) then
      match misSet.remove_min Q with
      | Some (Ss, Qr) =>
        let miSets :=
            Vertices.fold
              (fun j Q' =>
                 if VertexLtAndAdjacent j Ss then
                      let Sj := Vertices.inter Ss (ElementsLtEq j) in
                      let cndMIS :=
                          (Vertices.union
                             (Vertices.diff Sj (neighborhood j g))
                             (Vertices.add j Vertices.empty)) in
                      if maxInd.maximalIndSet
                           cndMIS
                           (SubgraphUpTo j)
                      then
                        let T := maxInd.MkMaximalIndSet cndMIS g in
                        (misSet.add T Q')
                      else
                        Q'
                 else
                   Q') (enumVertices g) Qr in
        out <- AllMIS_aux miSets (Ss :: output);
          Ret out
      | None => Ret output
      end
    else
      Ret output.
  
  Definition AllMIS : comp (list misSet.E.t):=
    let Ss := maxInd.MkMaximalIndSet Vertices.empty g in
    AllMIS_aux (misSet.add Ss misSet.empty) nil.
               
  End genMis.

End AllMIS.
