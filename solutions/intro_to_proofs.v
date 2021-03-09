(* ========================================================================== *]
 SIMPLE PROOFS IN COQ
[* ========================================================================== *)
Require Import Nat List Lia. 

(* -------------------------------------------------------------------------- *]
 To specify a property we are trying to prove we use the keyword `Lemma` or
 `Theorem`.

 To start writting the proof we use the keyword `Proof` and end it with the
 `Qed` keyword. This opens up the tactics environment.
[* -------------------------------------------------------------------------- *)

(* 
Lemma trivial_things (a : nat) (b : nat) (H0 : a = 1) (H1 : b = 2) :
    a + b = 3.
Proof.
    (* But how do we write proofs??? *)
Qed. 
*)


(* -------------------------------------------------------------------------- *]
 The tactics language in which we write proofs has a wide array of tools to
 use. We will focus on the essentials so that we can quickly get to more
 interesting examples.

 `assumption` 
    We have a hypothesis that matches what we want to prove

 `reflexivity` 
    It holds because `=` is reflexive, and our goal is to prove something along the lines of `x = x`

 `contradiction` 
    We have a contradiction in our hypotheses (and from that we are able to
    show anything).
[* -------------------------------------------------------------------------- *)

Lemma assumption_showcase (a : nat) (H0 : a = 1) :
    a = 1.
Proof.
    assumption.
Qed.

Lemma reflexivity_showcase (a : nat) :
    a = a.
Proof.
    reflexivity.
Qed.

(* We use a variable `P` for any proposition (like we often do in logic). *)
Lemma contradiction_showcase (P : Prop) (p_holds : P) (p_doesnt_hold : ~P):
    False. (* Can we prove that `False` is true?! *)
Proof.
    contradiction.
Qed.


(* -------------------------------------------------------------------------- *]
 The above tactics complete proofs. But we also require tactics that transform
 proofs.

 `simpl` 
    simplifies the terms in the goal /

 `unfold t`
    substitutes the term `t` with its definition (useful with functions)

 `rewrite H`
    if hypothesis `H` is of form `x = y` it replaces all occurencess of `x`
    with `y`

 NOTE: All of these tactics can also be used as `rewrite H0 in H1`, which uses
       the tactic in a hypothesis instead of our goal.

[* -------------------------------------------------------------------------- *)

Definition double x := x + x.

Lemma calculate_this (x y z : nat) (H0 : x = y + z) (H1 : double z = y):
    x = z + z + z.
Proof.
    rewrite H0.
    unfold double in H1.
    rewrite H1.
    reflexivity.
Qed.


(* -------------------------------------------------------------------------- *]
 Since the propositions we are trying to prove are writen in a logic, it is
 necessary to know at least some of the tactics for working with the logic.

 LOGIC IN GOALS
 
 `split`
    Transforms the goal `A /\ B` into two separate goals for `A` and `B`.
 
 `left / right`
    Transforms the goal `A \/ B` into `A` (or `B`) as it suffices to prove
    one side of an `or` statement.

 `intros`
    Transforms the goal `A -> B -> C -> ... -> P` into `P` but adds `A`, `B`, 
    `C`, ... to the hypotheses.
 `intros name1 name2 ...`
    You can (and often should) name the new hypotheses.

 `revert H`
    The opposite of `intros` where we take a hypothesis `H` and transform the
    goal of `A` back to `H -> A`.

 LOGIC IN HYPOTHESES
 
 `destruct`
    For `H : A /\ B` it separates the hypotheses into two new hypotheses, one 
    for `A` and one for `B`.

    For `H : A \/ B` it splits the proof into two goals. In the first case
    you have the hypothesis for `A` and in the second one for `B`.

 `apply H`
   If you have a `H : A -> B` and need to prove `B`, then by applying the
   implication it suffices to show `A`.

 `apply H0 in H1 as H2`
   For `H0 : A -> B` and `H1 : A` it generates a new hypothesis `H2 : B`.
   The naming part can be dropped in which case `H1 : A` is replaced with
   `H1 : B`.


 Since we now have tactics that also split our goals into multiple goals,
 we can use `+`, '-', or '*' as bullet points to focus each case separately
 (reduces visualclutter).
 
[* -------------------------------------------------------------------------- *)

Lemma example_for_logic (P Q R : Prop):
    (P \/ R) /\ (P \/ Q) -> ~P -> Q /\ R.
Proof.
    intros.
    destruct H.
    split.
    - destruct H1. contradiction. assumption.
    - destruct H. contradiction. assumption.
Qed.


(* -------------------------------------------------------------------------- *]
 For data types we also have some additional tactics.
 
 `discriminate`
    One of our hypotheses equates something that cannot be equal (more
    specifically equates two values that have different constructors, such
    as `0 = 1` or `nil = 1 :: nil`).

 `inversion`
    For `H : x :: xs = y :: ys` we can use `inversion H` to get `x = y` and
    `xs = ys`. It also does a rewrite of the equalities in the goal.

 `induction x`
    This tactic makes a case split on all possible ways to construct a value
    of type `x` and automatically generates induction hypotheses.
[* -------------------------------------------------------------------------- *)

Lemma discriminate_showcase (nonsense : 0 = 1):
    False.
Proof.
    discriminate.
Qed.

Lemma inversion_showcase A (x y : A) (xs ys : list A) :
    (x :: xs = y :: ys) -> xs = ys.
Proof.
    intros cons_equal.
    inversion cons_equal.
    reflexivity.
Qed.


Fixpoint length {A : Type} (lst : list A) :=
    match lst with
    | nil => 0
    | x :: xs => 1 + length xs
    end.

Lemma zero_length A (lst : list A) :
    length lst = 0 -> lst = nil.
Proof.
    intros zero_length.
    induction lst.
    reflexivity.
    simpl in zero_length.
    discriminate.
Qed.


(* -------------------------------------------------------------------------- *]
 It is good to see the basic tactics (as we sometimes need them), but to keep
 proofs short Coq provides tactics that help us automate the process.

 `auto`
    Tries to automatically complete the proof. If it cannot it simply leaves
    everything as is.

 `lia` (in older versions `omega`)
    Solver for numeric proofs. A true lifesaver (see example bellow).

 There are plent other usefull ways to help write shorter proofs, but we will
 stick to the basics.

 Do not forget you can use `_` to ask Coq to infer things for you.
[* -------------------------------------------------------------------------- *)

Fixpoint sum_nats n :=
    match n with
    | 0 => 0
    | S m => n + sum_nats m
    end. 

(* We multiply since division is not properly defined on naturals. *)
(* You do not want to write this proof by hand... *)
Lemma sum_of_naturals n:
    2 * (sum_nats n) = n * (1 + n).
Proof.
    induction n.
    - simpl. auto.
    - simpl. lia.
Qed.


(* -------------------------------------------------------------------------- *]
 PRACTICE: Show that if `P \/ Q -> R` and `P` hold, we can show that `R` holds.
 Do it without `auto`.
[* -------------------------------------------------------------------------- *)

Lemma practice P Q R :
    (P \/ Q -> R) -> P -> R.
Proof.
    intros. apply X. left. assumption.
Qed.
