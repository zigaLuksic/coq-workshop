(* ========================================================================== *]
 PROVING THINGS WE KNOW
[* ========================================================================== *)
Require Import Nat List Lia. 

(* -------------------------------------------------------------------------- *]
 Let's prove things we consider true in our everyday programming life.

 We start by defining some common functions for lists.
[* -------------------------------------------------------------------------- *)

(* Calculate length of list. *)
Fixpoint length {A} (lst : list A) :=
    match lst with
    | nil => 0
    | x :: xs => 1 + length xs
    end.

(* Concatenate two lists. *)
Fixpoint concat {A} (lst1 lst2 : list A) :=
    match lst1 with
    | nil => lst2
    | x :: xs => x :: (concat xs lst2)
    end.

(* Reverse a list. *)
Fixpoint reverse {A} (lst : list A) :=
    match lst with
    | nil => nil
    | x :: xs => concat (reverse xs) (x :: nil)
    end.

(* Apply function on all elements of list. *)
Fixpoint map {A B} (f : A -> B) (lst : list A) :=
    match lst with
    | nil => nil
    | x :: xs => f x :: map f xs
    end.

(* Compose two functions into a single one. *)
Definition compose {A B C} (f : B -> C) (g : A -> B) := 
    fun x => f (g x).


(* -------------------------------------------------------------------------- *]
 Most often we need properties that describe how different functions interact.
[* -------------------------------------------------------------------------- *)

Lemma length_concat {A} (lst1 lst2 : list A):
    length (concat lst1 lst2) = length lst1 + length lst2.
Proof.
    admit.
Qed.


Lemma length_map {A B} (lst : list A) (f : A -> B):
    length (map f lst) = length lst.
Proof.
    admit.
Qed.


Lemma map_compose {A B C} (lst : list A) (f : B -> C) (g : A -> B):
    map f (map g lst) = map (compose f g) lst.
Proof.
    admit.
Qed.


(* -------------------------------------------------------------------------- *]
 Sometimes we need to prove some auxiliary lemmas.
[* -------------------------------------------------------------------------- *)

(* These two seem obvious but must be shown. *)
Lemma concat_nil {A} (lst1 : list A):
    concat lst1 nil = lst1.
Proof.
    admit.
Qed.

Lemma concat_assoc {A} (lst1 lst2 lst3 : list A):
    concat (concat lst1 lst2) lst3 = concat lst1 (concat lst2 lst3).
Proof.
    admit.
Qed.

(* This is what we actually want. *)
Lemma reverse_concat {A} (lst1 lst2 : list A):
    reverse (concat lst1 lst2) = concat (reverse lst2) (reverse lst1).
Proof.
    admit.
Qed.


(* -------------------------------------------------------------------------- *]
 Induction needs to be performed at a general enough level in order to complete
 the following proof. If we try to first introduce all hypotheses, we get an
 induction hypothesis that is too weak.
[* -------------------------------------------------------------------------- *)

Fixpoint get_el {A} n (lst : list A) :=
    match lst, n with
    | nil, _ => None
    | x :: xs, 0 => Some x
    | x :: xs, S m => get_el m xs
    end.

Lemma get_fails {A} n (lst : list A) :
    length lst < n -> get_el n lst = None.
Proof.
    admit.
Qed.

(* -------------------------------------------------------------------------- *]
 By defining an inductive data type, Coq already know precisely what the
 appropriate induction principle is.
[* -------------------------------------------------------------------------- *)

Inductive tree {A} :=
| Empty : tree
| Node : tree -> A -> tree -> tree
.

Fixpoint mirror {A} (t : @tree A) :=
    match t with
    | Empty => Empty
    | Node l_t x r_t => Node (mirror r_t) x (mirror l_t)
    end.

Fixpoint height {A} (t : @tree A) :=
    match t with
    | Empty => 0
    | Node l_t x r_t => 1 + max (height l_t) (height r_t)
    end.


Lemma height_mirror {A} (t : @tree A) :
    height (mirror t) = height t.
Proof.
    admit.
Qed.


Lemma mirror_mirror {A} (t : @tree A) :
    mirror (mirror t) = t.
Proof.
    admit.
Qed.
