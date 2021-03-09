(* ========================================================================== *]
 THINGS COQ CAN DO
[* ========================================================================== *)
Require Import Nat List Lia.

Inductive tree {A} :=
| Empty : tree
| Node : tree -> A -> tree -> tree
.

Fixpoint height {A} (t : @tree A) :=
    match t with
    | Empty => 0
    | Node l_t x r_t => 1 + max (height l_t) (height r_t)
    end.

Fixpoint tree_map {A B} (f : A -> B) (t : @tree A) :=
    match t with
    | Empty => Empty
    | Node l_t x r_t => Node (tree_map f l_t) (f x) (tree_map f r_t)
    end.

(* -------------------------------------------------------------------------- *]
 A very useful thing is defining relations between terms (as propositions).
 This is something that we usually do by defining functions that map
 to `bool`, but by defining the relation inductively, allows us to perform
 induction on the 'proof' that two terms are related.

 Consider the following relation, that links trees with the same shape.
[* -------------------------------------------------------------------------- *)

Inductive same_shape {A B} : @tree A -> @tree B -> Prop :=
| both_empty : ???
| both_nodes lt_a lt_b a b rt_a rt_b : ???
.


(* -------------------------------------------------------------------------- *]
 Trees of the same shape have the same height, meaning that height is not
 impacted by the data of the tree (which is obvious to us, but sometimes
 obvious things turn out to be just our imagination...).
[* -------------------------------------------------------------------------- *)

Lemma same_shape_same_height {A B} (ta : @tree A) (tb : @tree B) :
    same_shape ta tb -> height ta = height tb.
Proof.
    admit.
Qed.


(* -------------------------------------------------------------------------- *]
 We can check that functions such as `map` do not alter the shape of the tree,
 only its data.

 Here we need to construct the proof that the trees have the same shape, so
 we apply the constructors of `same_shape`.
[* -------------------------------------------------------------------------- *)

Lemma map_preserves_shape {A B} (f : A -> B) (t : @tree A):
    same_shape t (tree_map f t).
Proof.
    admit.
Qed.


(* -------------------------------------------------------------------------- *]
 Coq also allows the use of 'values' in types. A standard example are vectors,
 which have their length specified as part of their type.
[* -------------------------------------------------------------------------- *)

Inductive vector {A} : nat -> Type :=
| Nil : vector 0
| Cons {n} : A -> vector n -> vector (S n)
.

Example vector_3 : vector 3 := Cons true (Cons true (Cons true Nil)).


(* -------------------------------------------------------------------------- *]
 Types now clearly state what happens to the vector length, which can help us
 avoid issues such as 'index out of range'.
[* -------------------------------------------------------------------------- *)

Fixpoint concat ??? :=
    match v1 with
    | Nil => v2
    | Cons x xs => Cons x (concat xs v2)
    end.

Compute (concat vector_3 vector_3).
