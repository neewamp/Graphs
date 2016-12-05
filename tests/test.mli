val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val max : nat -> nat -> nat

val min : nat -> nat -> nat

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

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end
 end

module OrderedTypeFacts :
 functor (O:OrderedType') ->
 sig
  module OrderTac :
   sig
    module OTF :
     sig
      type t = O.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    module TO :
     sig
      type t = OTF.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end
   end

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
 end

type positive =
| XI of positive
| XO of positive
| XH

module Pos :
 sig
  val succ : positive -> positive

  val eqb : positive -> positive -> bool
 end

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

module PairOrderedType :
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 sig
  type t = (O1.t, O2.t) prod

  val eq_dec : (O1.t, O2.t) prod -> (O1.t, O2.t) prod -> sumbool

  val compare : (O1.t, O2.t) prod -> (O1.t, O2.t) prod -> comparison
 end

module PositiveOrderedTypeBits :
 sig
  type t = positive

  val eqb : positive -> positive -> bool

  val eq_dec : positive -> positive -> sumbool

  val compare : positive -> positive -> comparison
 end

module MakeListOrdering :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = O.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

type color =
| Red
| Black

module Color :
 sig
  type t = color
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : X.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : X.t list -> tree -> X.t list

    val elements : tree -> X.t list

    val rev_elements_aux : X.t list -> tree -> X.t list

    val rev_elements : tree -> X.t list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> X.t -> tree -> bool

    val subsetr : (tree -> bool) -> X.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val singleton : elt -> tree

    val makeBlack : tree -> tree

    val makeRed : tree -> tree

    val lbal : tree -> X.t -> tree -> tree

    val rbal : tree -> X.t -> tree -> tree

    val rbal' : tree -> X.t -> tree -> tree

    val lbalS : tree -> X.t -> tree -> tree

    val rbalS : tree -> X.t -> tree -> tree

    val ins : X.t -> tree -> tree

    val add : X.t -> tree -> tree

    val append : tree -> tree -> tree

    val del : X.t -> tree -> tree

    val remove : X.t -> tree -> tree

    val delmin : tree -> elt -> tree -> (elt, tree) prod

    val remove_min : tree -> (elt, tree) prod option

    val bogus : (tree, elt list) prod

    val treeify_zero : elt list -> (tree, elt list) prod

    val treeify_one : elt list -> (tree, elt list) prod

    val treeify_cont :
      (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list)
      prod) -> elt list -> (tree, elt list) prod

    val treeify_aux : bool -> positive -> elt list -> (tree, elt list) prod

    val plength_aux : elt list -> positive -> positive

    val plength : elt list -> positive

    val treeify : elt list -> tree

    val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list

    val filter : (elt -> bool) -> t -> t

    val partition_aux :
      (elt -> bool) -> tree -> X.t list -> X.t list -> (X.t list, X.t list)
      prod

    val partition : (elt -> bool) -> t -> (t, t) prod

    val union_list : elt list -> elt list -> elt list -> elt list

    val linear_union : tree -> tree -> tree

    val inter_list : X.t list -> elt list -> elt list -> elt list

    val linear_inter : tree -> tree -> tree

    val diff_list : elt list -> elt list -> elt list -> elt list

    val linear_diff : tree -> tree -> tree

    val skip_red : tree -> tree

    val skip_black : tree -> tree

    val compare_height : tree -> tree -> tree -> tree -> comparison

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val ltb_tree : X.t -> tree -> bool

    val gtb_tree : X.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end

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

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    val rcase : (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase :
      (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1

    val rrcase' :
      (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1
   end

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  type elt = X.t

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option

  val remove_min : t_ -> (elt, t) prod option
 end

module Coq_myGraph :
 sig
  module Coq_pos :
   sig
    type t = positive

    val eqb : positive -> positive -> bool

    val eq_dec : positive -> positive -> sumbool

    val compare : positive -> positive -> comparison
   end

  module Vertices :
   sig
    module Raw :
     sig
      type elt = positive

      type tree =
      | Leaf
      | Node of Color.t * tree * positive * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : positive -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : positive list -> tree -> positive list

      val elements : tree -> positive list

      val rev_elements_aux : positive list -> tree -> positive list

      val rev_elements : tree -> positive list

      val cardinal : tree -> nat

      val maxdepth : tree -> nat

      val mindepth : tree -> nat

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        positive -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> positive -> tree -> bool

      val subsetr : (tree -> bool) -> positive -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val singleton : elt -> tree

      val makeBlack : tree -> tree

      val makeRed : tree -> tree

      val lbal : tree -> positive -> tree -> tree

      val rbal : tree -> positive -> tree -> tree

      val rbal' : tree -> positive -> tree -> tree

      val lbalS : tree -> positive -> tree -> tree

      val rbalS : tree -> positive -> tree -> tree

      val ins : positive -> tree -> tree

      val add : positive -> tree -> tree

      val append : tree -> tree -> tree

      val del : positive -> tree -> tree

      val remove : positive -> tree -> tree

      val delmin : tree -> elt -> tree -> (elt, tree) prod

      val remove_min : tree -> (elt, tree) prod option

      val bogus : (tree, elt list) prod

      val treeify_zero : elt list -> (tree, elt list) prod

      val treeify_one : elt list -> (tree, elt list) prod

      val treeify_cont :
        (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list)
        prod) -> elt list -> (tree, elt list) prod

      val treeify_aux : bool -> positive -> elt list -> (tree, elt list) prod

      val plength_aux : elt list -> positive -> positive

      val plength : elt list -> positive

      val treeify : elt list -> tree

      val filter_aux : (elt -> bool) -> tree -> positive list -> positive list

      val filter : (elt -> bool) -> t -> t

      val partition_aux :
        (elt -> bool) -> tree -> positive list -> positive list -> (positive
        list, positive list) prod

      val partition : (elt -> bool) -> t -> (t, t) prod

      val union_list : elt list -> elt list -> elt list -> elt list

      val linear_union : tree -> tree -> tree

      val inter_list : positive list -> elt list -> elt list -> elt list

      val linear_inter : tree -> tree -> tree

      val diff_list : elt list -> elt list -> elt list -> elt list

      val linear_diff : tree -> tree -> tree

      val skip_red : tree -> tree

      val skip_black : tree -> tree

      val compare_height : tree -> tree -> tree -> tree -> comparison

      val union : t -> t -> t

      val diff : t -> t -> t

      val inter : t -> t -> t

      val ltb_tree : positive -> tree -> bool

      val gtb_tree : positive -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = positive

            val compare : positive -> positive -> comparison

            val eq_dec : positive -> positive -> sumbool
           end

          module TO :
           sig
            type t = positive

            val compare : positive -> positive -> comparison

            val eq_dec : positive -> positive -> sumbool
           end
         end

        val eq_dec : positive -> positive -> sumbool

        val lt_dec : positive -> positive -> sumbool

        val eqb : positive -> positive -> bool
       end

      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Color.t * tree * positive * tree
      | R_min_elt_2 of tree * Color.t * tree * positive * tree * Color.t
         * tree * positive * tree * elt option * coq_R_min_elt

      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Color.t * tree * positive * tree
      | R_max_elt_2 of tree * Color.t * tree * positive * tree * Color.t
         * tree * positive * tree * elt option * coq_R_max_elt

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = positive

              val compare : positive -> positive -> comparison

              val eq_dec : positive -> positive -> sumbool
             end

            module TO :
             sig
              type t = positive

              val compare : positive -> positive -> comparison

              val eq_dec : positive -> positive -> sumbool
             end
           end

          val eq_dec : positive -> positive -> sumbool

          val lt_dec : positive -> positive -> sumbool

          val eqb : positive -> positive -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      val rcase :
        (tree -> positive -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

      val rrcase :
        (tree -> positive -> tree -> positive -> tree -> 'a1) -> (tree ->
        'a1) -> tree -> 'a1

      val rrcase' :
        (tree -> positive -> tree -> positive -> tree -> 'a1) -> (tree ->
        'a1) -> tree -> 'a1
     end

    module E :
     sig
      type t = positive

      val compare : positive -> positive -> comparison

      val eq_dec : positive -> positive -> sumbool
     end

    type elt = positive

    type t_ =
      Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val eq_dec : t -> t -> sumbool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option

    val remove_min : t_ -> (elt, t) prod option
   end

  module Edge :
   sig
    type t = (positive, positive) prod

    val eq_dec :
      (positive, positive) prod -> (positive, positive) prod -> sumbool

    val compare :
      (positive, positive) prod -> (positive, positive) prod -> comparison
   end

  module Edges :
   sig
    module Raw :
     sig
      type elt = (positive, positive) prod

      type tree =
      | Leaf
      | Node of Color.t * tree * (positive, positive) prod * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : (positive, positive) prod -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux :
        (positive, positive) prod list -> tree -> (positive, positive) prod
        list

      val elements : tree -> (positive, positive) prod list

      val rev_elements_aux :
        (positive, positive) prod list -> tree -> (positive, positive) prod
        list

      val rev_elements : tree -> (positive, positive) prod list

      val cardinal : tree -> nat

      val maxdepth : tree -> nat

      val mindepth : tree -> nat

      val for_all : (elt -> bool) -> tree -> bool

      val exists_ : (elt -> bool) -> tree -> bool

      type enumeration =
      | End
      | More of elt * tree * enumeration

      val cons : tree -> enumeration -> enumeration

      val compare_more :
        (positive, positive) prod -> (enumeration -> comparison) ->
        enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl :
        (tree -> bool) -> (positive, positive) prod -> tree -> bool

      val subsetr :
        (tree -> bool) -> (positive, positive) prod -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val singleton : elt -> tree

      val makeBlack : tree -> tree

      val makeRed : tree -> tree

      val lbal : tree -> (positive, positive) prod -> tree -> tree

      val rbal : tree -> (positive, positive) prod -> tree -> tree

      val rbal' : tree -> (positive, positive) prod -> tree -> tree

      val lbalS : tree -> (positive, positive) prod -> tree -> tree

      val rbalS : tree -> (positive, positive) prod -> tree -> tree

      val ins : (positive, positive) prod -> tree -> tree

      val add : (positive, positive) prod -> tree -> tree

      val append : tree -> tree -> tree

      val del : (positive, positive) prod -> tree -> tree

      val remove : (positive, positive) prod -> tree -> tree

      val delmin : tree -> elt -> tree -> (elt, tree) prod

      val remove_min : tree -> (elt, tree) prod option

      val bogus : (tree, elt list) prod

      val treeify_zero : elt list -> (tree, elt list) prod

      val treeify_one : elt list -> (tree, elt list) prod

      val treeify_cont :
        (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list)
        prod) -> elt list -> (tree, elt list) prod

      val treeify_aux : bool -> positive -> elt list -> (tree, elt list) prod

      val plength_aux : elt list -> positive -> positive

      val plength : elt list -> positive

      val treeify : elt list -> tree

      val filter_aux :
        (elt -> bool) -> tree -> (positive, positive) prod list -> (positive,
        positive) prod list

      val filter : (elt -> bool) -> t -> t

      val partition_aux :
        (elt -> bool) -> tree -> (positive, positive) prod list -> (positive,
        positive) prod list -> ((positive, positive) prod list, (positive,
        positive) prod list) prod

      val partition : (elt -> bool) -> t -> (t, t) prod

      val union_list : elt list -> elt list -> elt list -> elt list

      val linear_union : tree -> tree -> tree

      val inter_list :
        (positive, positive) prod list -> elt list -> elt list -> elt list

      val linear_inter : tree -> tree -> tree

      val diff_list : elt list -> elt list -> elt list -> elt list

      val linear_diff : tree -> tree -> tree

      val skip_red : tree -> tree

      val skip_black : tree -> tree

      val compare_height : tree -> tree -> tree -> tree -> comparison

      val union : t -> t -> t

      val diff : t -> t -> t

      val inter : t -> t -> t

      val ltb_tree : (positive, positive) prod -> tree -> bool

      val gtb_tree : (positive, positive) prod -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (positive, positive) prod

            val compare :
              (positive, positive) prod -> (positive, positive) prod ->
              comparison

            val eq_dec :
              (positive, positive) prod -> (positive, positive) prod ->
              sumbool
           end

          module TO :
           sig
            type t = (positive, positive) prod

            val compare :
              (positive, positive) prod -> (positive, positive) prod ->
              comparison

            val eq_dec :
              (positive, positive) prod -> (positive, positive) prod ->
              sumbool
           end
         end

        val eq_dec :
          (positive, positive) prod -> (positive, positive) prod -> sumbool

        val lt_dec :
          (positive, positive) prod -> (positive, positive) prod -> sumbool

        val eqb :
          (positive, positive) prod -> (positive, positive) prod -> bool
       end

      type coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Color.t * tree * (positive, positive) prod
         * tree
      | R_min_elt_2 of tree * Color.t * tree * (positive, positive) prod
         * tree * Color.t * tree * (positive, positive) prod * tree
         * elt option * coq_R_min_elt

      type coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Color.t * tree * (positive, positive) prod
         * tree
      | R_max_elt_2 of tree * Color.t * tree * (positive, positive) prod
         * tree * Color.t * tree * (positive, positive) prod * tree
         * elt option * coq_R_max_elt

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = (positive, positive) prod

              val compare :
                (positive, positive) prod -> (positive, positive) prod ->
                comparison

              val eq_dec :
                (positive, positive) prod -> (positive, positive) prod ->
                sumbool
             end

            module TO :
             sig
              type t = (positive, positive) prod

              val compare :
                (positive, positive) prod -> (positive, positive) prod ->
                comparison

              val eq_dec :
                (positive, positive) prod -> (positive, positive) prod ->
                sumbool
             end
           end

          val eq_dec :
            (positive, positive) prod -> (positive, positive) prod -> sumbool

          val lt_dec :
            (positive, positive) prod -> (positive, positive) prod -> sumbool

          val eqb :
            (positive, positive) prod -> (positive, positive) prod -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      val rcase :
        (tree -> (positive, positive) prod -> tree -> 'a1) -> (tree -> 'a1)
        -> tree -> 'a1

      val rrcase :
        (tree -> (positive, positive) prod -> tree -> (positive, positive)
        prod -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

      val rrcase' :
        (tree -> (positive, positive) prod -> tree -> (positive, positive)
        prod -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1
     end

    module E :
     sig
      type t = (positive, positive) prod

      val compare :
        (positive, positive) prod -> (positive, positive) prod -> comparison

      val eq_dec :
        (positive, positive) prod -> (positive, positive) prod -> sumbool
     end

    type elt = (positive, positive) prod

    type t_ =
      Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val eq_dec : t -> t -> sumbool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option

    val remove_min : t_ -> (elt, t) prod option
   end

  type edge = Edges.elt

  type v_set = Vertices.t

  type e_set = Edges.t

  type coq_Graph = { graphVertices : v_set; graphEdges : e_set }

  val graphVertices : coq_Graph -> v_set

  val graphEdges : coq_Graph -> e_set

  type t = coq_Graph

  val empty : coq_Graph

  val enumEdges : coq_Graph -> Edges.t

  val addVertex : Vertices.elt -> t -> t

  val coq_Vertices_in_dec1 :
    (Vertices.elt, Vertices.elt) prod -> coq_Graph -> sumbool

  val coq_Vertices_in_dec2 :
    (Vertices.elt, Vertices.elt) prod -> coq_Graph -> sumbool

  val coq_Vertices_in_dec :
    (Vertices.elt, Vertices.elt) prod -> coq_Graph -> sumbool

  val addEdge : edge -> t -> t

  val neighborhood : Vertices.elt -> t -> Vertices.t
 end

val graph1 : Coq_myGraph.t

val test1 : Coq_myGraph.Vertices.elt list
