(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ c =
  compareSpec2Type c

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' ->
    (match m with
     | O -> n
     | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' ->
    (match m with
     | O -> O
     | S m' -> S (min n' m'))

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    O.eq_dec
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> Left
     | _ -> Right)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> true
    | Right -> false
 end

type positive =
| XI of positive
| XO of positive
| XH

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
 end

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a::l0 -> rev_append l0 (a::l')

module PairOrderedType =
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 struct
  type t = (O1.t, O2.t) prod

  (** val eq_dec : (O1.t, O2.t) prod -> (O1.t, O2.t) prod -> sumbool **)

  let eq_dec x y =
    let Pair (x1, x2) = x in
    let Pair (y1, y2) = y in
    let s = O1.eq_dec x1 y1 in
    (match s with
     | Left -> O2.eq_dec x2 y2
     | Right -> Right)

  (** val compare : (O1.t, O2.t) prod -> (O1.t, O2.t) prod -> comparison **)

  let compare x y =
    match O1.compare (fst x) (fst y) with
    | Eq -> O2.compare (snd x) (snd y)
    | x0 -> x0
 end

module PositiveOrderedTypeBits =
 struct
  type t = positive

  (** val eqb : positive -> positive -> bool **)

  let eqb =
    Pos.eqb

  (** val eq_dec : positive -> positive -> sumbool **)

  let eq_dec x y =
    let b = Pos.eqb x y in if b then Left else Right

  (** val compare : positive -> positive -> comparison **)

  let rec compare x y =
    match x with
    | XI x0 ->
      (match y with
       | XI y0 -> compare x0 y0
       | _ -> Gt)
    | XO x0 ->
      (match y with
       | XO y0 -> compare x0 y0
       | _ -> Lt)
    | XH ->
      (match y with
       | XI _ -> Lt
       | XO _ -> Gt
       | XH -> Eq)
 end

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

type color =
| Red
| Black

module Color =
 struct
  type t = color
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw =
   struct
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    (** val empty : tree **)

    let empty =
      Leaf

    (** val is_empty : tree -> bool **)

    let is_empty = function
    | Leaf -> true
    | Node (_, _, _, _) -> false

    (** val mem : X.t -> tree -> bool **)

    let rec mem x = function
    | Leaf -> false
    | Node (_, l, k, r) ->
      (match X.compare x k with
       | Eq -> true
       | Lt -> mem x l
       | Gt -> mem x r)

    (** val min_elt : tree -> elt option **)

    let rec min_elt = function
    | Leaf -> None
    | Node (_, l, x, _) ->
      (match l with
       | Leaf -> Some x
       | Node (_, _, _, _) -> min_elt l)

    (** val max_elt : tree -> elt option **)

    let rec max_elt = function
    | Leaf -> None
    | Node (_, _, x, r) ->
      (match r with
       | Leaf -> Some x
       | Node (_, _, _, _) -> max_elt r)

    (** val choose : tree -> elt option **)

    let choose =
      min_elt

    (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

    let rec fold f t0 base =
      match t0 with
      | Leaf -> base
      | Node (_, l, x, r) -> fold f r (f x (fold f l base))

    (** val elements_aux : X.t list -> tree -> X.t list **)

    let rec elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> elements_aux (x::(elements_aux acc r)) l

    (** val elements : tree -> X.t list **)

    let elements =
      elements_aux []

    (** val rev_elements_aux : X.t list -> tree -> X.t list **)

    let rec rev_elements_aux acc = function
    | Leaf -> acc
    | Node (_, l, x, r) -> rev_elements_aux (x::(rev_elements_aux acc l)) r

    (** val rev_elements : tree -> X.t list **)

    let rev_elements =
      rev_elements_aux []

    (** val cardinal : tree -> nat **)

    let rec cardinal = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (add (cardinal l) (cardinal r))

    (** val maxdepth : tree -> nat **)

    let rec maxdepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (max (maxdepth l) (maxdepth r))

    (** val mindepth : tree -> nat **)

    let rec mindepth = function
    | Leaf -> O
    | Node (_, l, _, r) -> S (min (mindepth l) (mindepth r))

    (** val for_all : (elt -> bool) -> tree -> bool **)

    let rec for_all f = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      if if f x then for_all f l else false then for_all f r else false

    (** val exists_ : (elt -> bool) -> tree -> bool **)

    let rec exists_ f = function
    | Leaf -> false
    | Node (_, l, x, r) ->
      if if f x then true else exists_ f l then true else exists_ f r

    type enumeration =
    | End
    | More of elt * tree * enumeration

    (** val cons : tree -> enumeration -> enumeration **)

    let rec cons s e =
      match s with
      | Leaf -> e
      | Node (_, l, x, r) -> cons l (More (x, r, e))

    (** val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

    let compare_more x1 cont = function
    | End -> Gt
    | More (x2, r2, e3) ->
      (match X.compare x1 x2 with
       | Eq -> cont (cons r2 e3)
       | x -> x)

    (** val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison **)

    let rec compare_cont s1 cont e2 =
      match s1 with
      | Leaf -> cont e2
      | Node (_, l1, x1, r1) ->
        compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

    (** val compare_end : enumeration -> comparison **)

    let compare_end = function
    | End -> Eq
    | More (_, _, _) -> Lt

    (** val compare : tree -> tree -> comparison **)

    let compare s1 s2 =
      compare_cont s1 compare_end (cons s2 End)

    (** val equal : tree -> tree -> bool **)

    let equal s1 s2 =
      match compare s1 s2 with
      | Eq -> true
      | _ -> false

    (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

    let rec subsetl subset_l1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_l1 l2
       | Lt -> subsetl subset_l1 x1 l2
       | Gt -> if mem x1 r2 then subset_l1 s2 else false)

    (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

    let rec subsetr subset_r1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (_, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_r1 r2
       | Lt -> if mem x1 l2 then subset_r1 s2 else false
       | Gt -> subsetr subset_r1 x1 r2)

    (** val subset : tree -> tree -> bool **)

    let rec subset s1 s2 =
      match s1 with
      | Leaf -> true
      | Node (_, l1, x1, r1) ->
        (match s2 with
         | Leaf -> false
         | Node (_, l2, x2, r2) ->
           (match X.compare x1 x2 with
            | Eq -> if subset l1 l2 then subset r1 r2 else false
            | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
            | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

    type t = tree

    (** val singleton : elt -> tree **)

    let singleton k =
      Node (Black, Leaf, k, Leaf)

    (** val makeBlack : tree -> tree **)

    let makeBlack = function
    | Leaf -> Leaf
    | Node (_, a, x, b) -> Node (Black, a, x, b)

    (** val makeRed : tree -> tree **)

    let makeRed = function
    | Leaf -> Leaf
    | Node (_, a, x, b) -> Node (Red, a, x, b)

    (** val lbal : tree -> X.t -> tree -> tree **)

    let lbal l k r =
      match l with
      | Leaf -> Node (Black, l, k, r)
      | Node (t0, a, x, c) ->
        (match t0 with
         | Red ->
           (match a with
            | Leaf ->
              (match c with
               | Leaf -> Node (Black, l, k, r)
               | Node (t1, b, y, c0) ->
                 (match t1 with
                  | Red ->
                    Node (Red, (Node (Black, a, x, b)), y, (Node (Black, c0,
                      k, r)))
                  | Black -> Node (Black, l, k, r)))
            | Node (t1, a0, x0, b) ->
              (match t1 with
               | Red ->
                 Node (Red, (Node (Black, a0, x0, b)), x, (Node (Black, c, k,
                   r)))
               | Black ->
                 (match c with
                  | Leaf -> Node (Black, l, k, r)
                  | Node (t2, b0, y, c0) ->
                    (match t2 with
                     | Red ->
                       Node (Red, (Node (Black, a, x, b0)), y, (Node (Black,
                         c0, k, r)))
                     | Black -> Node (Black, l, k, r)))))
         | Black -> Node (Black, l, k, r))

    (** val rbal : tree -> X.t -> tree -> tree **)

    let rbal l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b, y, d) ->
      (match t0 with
       | Red ->
         (match b with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z, d0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c, z,
                    d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b0, y0, c) ->
            (match t1 with
             | Red ->
               Node (Red, (Node (Black, l, k, b0)), y0, (Node (Black, c, y,
                 d)))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b)), y, (Node (Black, c0,
                       z, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

    (** val rbal' : tree -> X.t -> tree -> tree **)

    let rbal' l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b, z, d) ->
      (match t0 with
       | Red ->
         (match b with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z0, d0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c, z0,
                    d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b0, y, c) ->
            (match t1 with
             | Red ->
               (match d with
                | Leaf ->
                  Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c, z,
                    d)))
                | Node (t2, c0, z0, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                       z0, d0)))
                   | Black ->
                     Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c,
                       z, d)))))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z0, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b)), z, (Node (Black, c0,
                       z0, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))

    (** val lbalS : tree -> X.t -> tree -> tree **)

    let lbalS l k r =
      match l with
      | Leaf ->
        (match r with
         | Leaf -> Node (Red, l, k, r)
         | Node (t0, a, z, c) ->
           (match t0 with
            | Red ->
              (match a with
               | Leaf -> Node (Red, l, k, r)
               | Node (t1, a0, y, b) ->
                 (match t1 with
                  | Red -> Node (Red, l, k, r)
                  | Black ->
                    Node (Red, (Node (Black, l, k, a0)), y,
                      (rbal' b z (makeRed c)))))
            | Black -> rbal' l k (Node (Red, a, z, c))))
      | Node (t0, a, x, b) ->
        (match t0 with
         | Red -> Node (Red, (Node (Black, a, x, b)), k, r)
         | Black ->
           (match r with
            | Leaf -> Node (Red, l, k, r)
            | Node (t1, a0, z, c) ->
              (match t1 with
               | Red ->
                 (match a0 with
                  | Leaf -> Node (Red, l, k, r)
                  | Node (t2, a1, y, b0) ->
                    (match t2 with
                     | Red -> Node (Red, l, k, r)
                     | Black ->
                       Node (Red, (Node (Black, l, k, a1)), y,
                         (rbal' b0 z (makeRed c)))))
               | Black -> rbal' l k (Node (Red, a0, z, c)))))

    (** val rbalS : tree -> X.t -> tree -> tree **)

    let rbalS l k r = match r with
    | Leaf ->
      (match l with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, x, b) ->
         (match t0 with
          | Red ->
            (match b with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, b0, y, c) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black ->
                  Node (Red, (lbal (makeRed a) x b0), y, (Node (Black, c, k,
                    r)))))
          | Black -> lbal (Node (Red, a, x, b)) k r))
    | Node (t0, b, y, c) ->
      (match t0 with
       | Red -> Node (Red, l, k, (Node (Black, b, y, c)))
       | Black ->
         (match l with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a, x, b0) ->
            (match t1 with
             | Red ->
               (match b0 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, b1, y0, c0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black ->
                     Node (Red, (lbal (makeRed a) x b1), y0, (Node (Black,
                       c0, k, r)))))
             | Black -> lbal (Node (Red, a, x, b0)) k r)))

    (** val ins : X.t -> tree -> tree **)

    let rec ins x s = match s with
    | Leaf -> Node (Red, Leaf, x, Leaf)
    | Node (c, l, y, r) ->
      (match X.compare x y with
       | Eq -> s
       | Lt ->
         (match c with
          | Red -> Node (Red, (ins x l), y, r)
          | Black -> lbal (ins x l) y r)
       | Gt ->
         (match c with
          | Red -> Node (Red, l, y, (ins x r))
          | Black -> rbal l y (ins x r)))

    (** val add : X.t -> tree -> tree **)

    let add x s =
      makeBlack (ins x s)

    (** val append : tree -> tree -> tree **)

    let rec append l = match l with
    | Leaf -> (fun r -> r)
    | Node (lc, ll, lx, lr) ->
      let rec append_l r = match r with
      | Leaf -> l
      | Node (rc, rl, rx, rr) ->
        (match lc with
         | Red ->
           (match rc with
            | Red ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
               | Node (t0, lr', x, rl') ->
                 (match t0 with
                  | Red ->
                    Node (Red, (Node (Red, ll, lx, lr')), x, (Node (Red, rl',
                      rx, rr)))
                  | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
            | Black -> Node (Red, ll, lx, (append lr r)))
         | Black ->
           (match rc with
            | Red -> Node (Red, (append_l rl), rx, rr)
            | Black ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
               | Node (t0, lr', x, rl') ->
                 (match t0 with
                  | Red ->
                    Node (Red, (Node (Black, ll, lx, lr')), x, (Node (Black,
                      rl', rx, rr)))
                  | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
      in append_l

    (** val del : X.t -> tree -> tree **)

    let rec del x = function
    | Leaf -> Leaf
    | Node (_, a, y, b) ->
      (match X.compare x y with
       | Eq -> append a b
       | Lt ->
         (match a with
          | Leaf -> Node (Red, (del x a), y, b)
          | Node (t1, _, _, _) ->
            (match t1 with
             | Red -> Node (Red, (del x a), y, b)
             | Black -> lbalS (del x a) y b))
       | Gt ->
         (match b with
          | Leaf -> Node (Red, a, y, (del x b))
          | Node (t1, _, _, _) ->
            (match t1 with
             | Red -> Node (Red, a, y, (del x b))
             | Black -> rbalS a y (del x b))))

    (** val remove : X.t -> tree -> tree **)

    let remove x t0 =
      makeBlack (del x t0)

    (** val delmin : tree -> elt -> tree -> (elt, tree) prod **)

    let rec delmin l x r =
      match l with
      | Leaf -> Pair (x, r)
      | Node (lc, ll, lx, lr) ->
        let Pair (k, l') = delmin ll lx lr in
        (match lc with
         | Red -> Pair (k, (Node (Red, l', x, r)))
         | Black -> Pair (k, (lbalS l' x r)))

    (** val remove_min : tree -> (elt, tree) prod option **)

    let remove_min = function
    | Leaf -> None
    | Node (_, l, x, r) ->
      let Pair (k, t1) = delmin l x r in Some (Pair (k, (makeBlack t1)))

    (** val bogus : (tree, elt list) prod **)

    let bogus =
      Pair (Leaf, [])

    (** val treeify_zero : elt list -> (tree, elt list) prod **)

    let treeify_zero acc =
      Pair (Leaf, acc)

    (** val treeify_one : elt list -> (tree, elt list) prod **)

    let treeify_one = function
    | [] -> bogus
    | x::acc0 -> Pair ((Node (Red, Leaf, x, Leaf)), acc0)

    (** val treeify_cont :
        (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list)
        prod) -> elt list -> (tree, elt list) prod **)

    let treeify_cont f g acc =
      let Pair (l, l0) = f acc in
      (match l0 with
       | [] -> bogus
       | x::acc0 ->
         let Pair (r, acc1) = g acc0 in Pair ((Node (Black, l, x, r)), acc1))

    (** val treeify_aux :
        bool -> positive -> elt list -> (tree, elt list) prod **)

    let rec treeify_aux pred = function
    | XI n0 -> treeify_cont (treeify_aux false n0) (treeify_aux pred n0)
    | XO n0 -> treeify_cont (treeify_aux pred n0) (treeify_aux true n0)
    | XH -> if pred then treeify_zero else treeify_one

    (** val plength_aux : elt list -> positive -> positive **)

    let rec plength_aux l p =
      match l with
      | [] -> p
      | _::l0 -> plength_aux l0 (Pos.succ p)

    (** val plength : elt list -> positive **)

    let plength l =
      plength_aux l XH

    (** val treeify : elt list -> tree **)

    let treeify l =
      fst (treeify_aux true (plength l) l)

    (** val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list **)

    let rec filter_aux f s acc =
      match s with
      | Leaf -> acc
      | Node (_, l, k, r) ->
        let acc0 = filter_aux f r acc in
        if f k then filter_aux f l (k::acc0) else filter_aux f l acc0

    (** val filter : (elt -> bool) -> t -> t **)

    let filter f s =
      treeify (filter_aux f s [])

    (** val partition_aux :
        (elt -> bool) -> tree -> X.t list -> X.t list -> (X.t list, X.t list)
        prod **)

    let rec partition_aux f s acc1 acc2 =
      match s with
      | Leaf -> Pair (acc1, acc2)
      | Node (_, sl, k, sr) ->
        let Pair (acc3, acc4) = partition_aux f sr acc1 acc2 in
        if f k
        then partition_aux f sl (k::acc3) acc4
        else partition_aux f sl acc3 (k::acc4)

    (** val partition : (elt -> bool) -> t -> (t, t) prod **)

    let partition f s =
      let Pair (ok, ko) = partition_aux f s [] [] in
      Pair ((treeify ok), (treeify ko))

    (** val union_list : elt list -> elt list -> elt list -> elt list **)

    let rec union_list l1 = match l1 with
    | [] -> rev_append
    | x::l1' ->
      let rec union_l1 l2 acc =
        match l2 with
        | [] -> rev_append l1 acc
        | y::l2' ->
          (match X.compare x y with
           | Eq -> union_list l1' l2' (x::acc)
           | Lt -> union_l1 l2' (y::acc)
           | Gt -> union_list l1' l2 (x::acc))
      in union_l1

    (** val linear_union : tree -> tree -> tree **)

    let linear_union s1 s2 =
      treeify (union_list (rev_elements s1) (rev_elements s2) [])

    (** val inter_list : X.t list -> elt list -> elt list -> elt list **)

    let rec inter_list = function
    | [] -> (fun _ acc -> acc)
    | x::l1' ->
      let rec inter_l1 l2 acc =
        match l2 with
        | [] -> acc
        | y::l2' ->
          (match X.compare x y with
           | Eq -> inter_list l1' l2' (x::acc)
           | Lt -> inter_l1 l2' acc
           | Gt -> inter_list l1' l2 acc)
      in inter_l1

    (** val linear_inter : tree -> tree -> tree **)

    let linear_inter s1 s2 =
      treeify (inter_list (rev_elements s1) (rev_elements s2) [])

    (** val diff_list : elt list -> elt list -> elt list -> elt list **)

    let rec diff_list l1 = match l1 with
    | [] -> (fun _ acc -> acc)
    | x::l1' ->
      let rec diff_l1 l2 acc =
        match l2 with
        | [] -> rev_append l1 acc
        | y::l2' ->
          (match X.compare x y with
           | Eq -> diff_list l1' l2' acc
           | Lt -> diff_l1 l2' acc
           | Gt -> diff_list l1' l2 (x::acc))
      in diff_l1

    (** val linear_diff : tree -> tree -> tree **)

    let linear_diff s1 s2 =
      treeify (diff_list (rev_elements s1) (rev_elements s2) [])

    (** val skip_red : tree -> tree **)

    let skip_red t0 = match t0 with
    | Leaf -> t0
    | Node (t1, t', _, _) ->
      (match t1 with
       | Red -> t'
       | Black -> t0)

    (** val skip_black : tree -> tree **)

    let skip_black t0 =
      match skip_red t0 with
      | Leaf -> Leaf
      | Node (t1, t', t2, t3) ->
        (match t1 with
         | Red -> Node (Red, t', t2, t3)
         | Black -> t')

    (** val compare_height : tree -> tree -> tree -> tree -> comparison **)

    let rec compare_height s1x s1 s2 s2x =
      match skip_red s1x with
      | Leaf ->
        (match skip_red s1 with
         | Leaf ->
           (match skip_red s2x with
            | Leaf -> Eq
            | Node (_, _, _, _) -> Lt)
         | Node (_, s1', _, _) ->
           (match skip_red s2 with
            | Leaf -> Eq
            | Node (_, s2', _, _) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (_, s2x', _, _) ->
                 compare_height Leaf s1' s2' (skip_black s2x'))))
      | Node (_, s1x', _, _) ->
        (match skip_red s1 with
         | Leaf ->
           (match skip_red s2 with
            | Leaf ->
              (match skip_red s2x with
               | Leaf -> Gt
               | Node (_, _, _, _) -> Lt)
            | Node (_, _, _, _) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (_, _, _, _) -> Lt))
         | Node (_, s1', _, _) ->
           (match skip_red s2 with
            | Leaf -> Gt
            | Node (_, s2', _, _) ->
              (match skip_red s2x with
               | Leaf -> compare_height (skip_black s1x') s1' s2' Leaf
               | Node (_, s2x', _, _) ->
                 compare_height (skip_black s1x') s1' s2' (skip_black s2x'))))

    (** val union : t -> t -> t **)

    let union t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_union t1 t2
      | Lt -> fold add t1 t2
      | Gt -> fold add t2 t1

    (** val diff : t -> t -> t **)

    let diff t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_diff t1 t2
      | Lt -> filter (fun k -> negb (mem k t2)) t1
      | Gt -> fold remove t2 t1

    (** val inter : t -> t -> t **)

    let inter t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_inter t1 t2
      | Lt -> filter (fun k -> mem k t2) t1
      | Gt -> filter (fun k -> mem k t1) t2

    (** val ltb_tree : X.t -> tree -> bool **)

    let rec ltb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match X.compare x y with
       | Gt -> if ltb_tree x l then ltb_tree x r else false
       | _ -> false)

    (** val gtb_tree : X.t -> tree -> bool **)

    let rec gtb_tree x = function
    | Leaf -> true
    | Node (_, l, y, r) ->
      (match X.compare x y with
       | Lt -> if gtb_tree x l then gtb_tree x r else false
       | _ -> false)

    (** val isok : tree -> bool **)

    let rec isok = function
    | Leaf -> true
    | Node (_, l, x, r) ->
      if if if isok l then isok r else false then ltb_tree x l else false
      then gtb_tree x r
      else false

    module MX = OrderedTypeFacts(X)

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_max_elt

    module L = MakeListOrdering(X)

    (** val flatten_e : enumeration -> elt list **)

    let rec flatten_e = function
    | End -> []
    | More (x, t0, r) -> x::(app (elements t0) (flatten_e r))

    (** val rcase :
        (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)

    let rcase f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x, b) ->
      (match t1 with
       | Red -> f a x b
       | Black -> g t0)

    (** val rrcase :
        (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree
        -> 'a1 **)

    let rrcase f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b, y, c0) ->
               (match t2 with
                | Red -> f a x b y c0
                | Black -> g t0))
          | Node (t2, a0, x0, b) ->
            (match t2 with
             | Red -> f a0 x0 b x c
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b0, y, c0) ->
                  (match t3 with
                   | Red -> f a x b0 y c0
                   | Black -> g t0))))
       | Black -> g t0)

    (** val rrcase' :
        (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree
        -> 'a1 **)

    let rrcase' f g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, y, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b, y0, c0) ->
               (match t2 with
                | Red -> f a y b y0 c0
                | Black -> g t0))
          | Node (t2, a0, x, b) ->
            (match t2 with
             | Red ->
               (match c with
                | Leaf -> f a0 x b y c
                | Node (t3, b0, y0, c0) ->
                  (match t3 with
                   | Red -> f a y b0 y0 c0
                   | Black -> f a0 x b y c))
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b0, y0, c0) ->
                  (match t3 with
                   | Red -> f a y b0 y0 c0
                   | Black -> g t0))))
       | Black -> g t0)
   end

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton x =
    Raw.singleton x

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in Pair ((fst p), (snd p))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then Left else Right

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)

  (** val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option **)

  let mk_opt_t = function
  | Some p -> let Pair (k, s') = p in Some (Pair (k, s'))
  | None -> None

  (** val remove_min : t_ -> (elt, t) prod option **)

  let remove_min s =
    mk_opt_t (Raw.remove_min (this s))
 end

module Coq_myGraph =
 struct
  module Coq_pos = PositiveOrderedTypeBits

  module Vertices = Make(Coq_pos)

  module Edge = PairOrderedType(Coq_pos)(Coq_pos)

  module Edges = Make(Edge)

  type edge = Edges.elt

  type v_set = Vertices.t

  type e_set = Edges.t

  type coq_Graph = { graphVertices : v_set; graphEdges : e_set }

  (** val graphVertices : coq_Graph -> v_set **)

  let graphVertices x = x.graphVertices

  (** val graphEdges : coq_Graph -> e_set **)

  let graphEdges x = x.graphEdges

  type t = coq_Graph

  (** val empty : coq_Graph **)

  let empty =
    { graphVertices = Vertices.empty; graphEdges = Edges.empty }

  (** val enumEdges : coq_Graph -> Edges.t **)

  let enumEdges g =
    g.graphEdges

  (** val addVertex : Vertices.elt -> t -> t **)

  let addVertex v g =
    { graphVertices = (Vertices.add v g.graphVertices); graphEdges =
      g.graphEdges }

  (** val coq_Vertices_in_dec1 :
      (Vertices.elt, Vertices.elt) prod -> coq_Graph -> sumbool **)

  let coq_Vertices_in_dec1 e g =
    if Vertices.mem (fst e) g.graphVertices then Left else Right

  (** val coq_Vertices_in_dec2 :
      (Vertices.elt, Vertices.elt) prod -> coq_Graph -> sumbool **)

  let coq_Vertices_in_dec2 e g =
    if Vertices.mem (snd e) g.graphVertices then Left else Right

  (** val coq_Vertices_in_dec :
      (Vertices.elt, Vertices.elt) prod -> coq_Graph -> sumbool **)

  let coq_Vertices_in_dec e g =
    let s = coq_Vertices_in_dec1 e g in
    (match s with
     | Left -> coq_Vertices_in_dec2 e g
     | Right -> Right)

  (** val addEdge : edge -> t -> t **)

  let addEdge e g =
    match coq_Vertices_in_dec e g with
    | Left ->
      { graphVertices = g.graphVertices; graphEdges =
        (Edges.add e g.graphEdges) }
    | Right -> g

  (** val neighborhood : Vertices.elt -> t -> Vertices.t **)

  let neighborhood v g =
    Edges.fold (fun edge0 e ->
      if Pos.eqb (fst edge0) v then Vertices.add (snd edge0) e else e)
      (enumEdges g) Vertices.empty
 end

(** val graph1 : Coq_myGraph.t **)

let graph1 =
  Coq_myGraph.addEdge (Pair (1, (2)))
    (Coq_myGraph.addEdge (Pair (1, (3)))
      (Coq_myGraph.addEdge (Pair ((2), (2)))
        (Coq_myGraph.addVertex 1
          (Coq_myGraph.addVertex (2)
            (Coq_myGraph.addVertex (3)
              (Coq_myGraph.addVertex (4) Coq_myGraph.empty))))))

(** val test1 : Coq_myGraph.Vertices.elt list **)

let test1 =
  Coq_myGraph.Vertices.elements (Coq_myGraph.neighborhood XH graph1)
let rec int_of_pos p = 
(match p with
 |XH -> 1
|XO p' -> 2 * (int_of_pos p')
|XI p' -> 2* (int_of_pos p') + 1)

let rec printer l =
(match l with
| [] -> Printf.printf 
|  (h:: t) -> Printf.printf "%d " h; printer t)

let print1 =
printer (List.map int_of_pos (test1));;

let () = Printf.printf "\n";;
let time f=
let t = Sys.time() in
let fx = f in
Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
fx

let t = time print1 ;;