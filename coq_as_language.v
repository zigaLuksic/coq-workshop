(* ========================================================================== *]
 COQ AS A REGULAR PROGRAMMING LANGUAGE 
[* ========================================================================== *)

(* We import the librariy for working with natural numbers and lists. *)
Require Import Nat List. 

(* -------------------------------------------------------------------------- *]
 To define values use the `Definition` keyword. When defining things use the
 `:=` symbol. 

 Statements in Coq are ended with `.` (a bit similar to `;` in most languages.
[* -------------------------------------------------------------------------- *)
Definition twelve := 12.
Definition sum_four_and_four := 4 + 4.

(* You can also use `Example` instead of `Definition` for readability. *)
Example let_statement_example := 
    let a := 2 in
    let b := 3 in
    a * b - 2.


(* -------------------------------------------------------------------------- *]
 A simple way to display defined values is to use `Print`.
[* -------------------------------------------------------------------------- *)

Print twelve.
Print let_statement_example.


(* -------------------------------------------------------------------------- *]
 Coq does not evaluate unless specifically asked to. One way to do this is to
 use the `Compute` statement.
[* -------------------------------------------------------------------------- *)

Compute let_statement_example.


(* -------------------------------------------------------------------------- *]
 Defining functions uses the same commands, with the added notation for
 defining anonymous functions `fun ??? => ???`.
[* -------------------------------------------------------------------------- *)

Definition sum_three x y z := x + y + z.
Definition sum_three_anon := fun x y z => x + y + z.


(* -------------------------------------------------------------------------- *]
 At the start of the file we also imported the module `List` for using lists.
 The empty list is `nil` and for the constructor `cons x xs` we also have the
 sugared syntax `x :: xs`.
[* -------------------------------------------------------------------------- *)

Example list_of_ones := 1 :: 1 :: 1 :: nil.
Example raw_list_of_twos := cons 2 (cons 2 (cons 2 nil)).


(* -------------------------------------------------------------------------- *]
 We can extract data with `match` statements, where we list the patterns for
 all constructors. The `match` statement needs to be ended with the `end`
 keyword.
[* -------------------------------------------------------------------------- *)

Definition starts_with_0 lst :=
    match lst with
    | nil => false
    | 0 :: _ => true
    | _ :: _ => true
    end.


(* -------------------------------------------------------------------------- *]
 To use recursive functions we need to use `Fixpoint` instead of `Definition`.

 WARNING: Coq is VERY careful when it comes to recursion and requires to know
 that it will always terminate!
[* -------------------------------------------------------------------------- *)

Fixpoint sum_elements lst :=
    match lst with
    | nil => 0
    | x :: xs => x + sum_elements xs
    end.

(* Coq does not know how to prove that the following function terminates. *)
(*
Fixpoint double_n_times x n := 
    if n =? 0 then x else double_n_times (2*x) (n-1).
*)

(* 

NOTE: `=?` is a comparison that returns a `bool`. The symbol `=` is used as
equality in propositions when proving properties.

The definition with conditionals does not work, because Coq cannot
automatically detect that the recursion will terminate. 

We can instead use the match statement for natural numbers. Natural numbers are
defined with the Peano axioms, so a natural number is either 0 or a successor
`S` of a natural number.
*)

Fixpoint double_n_times x n :=
    match n with
    | 0 => x
    | S m => double_n_times (2*x) m
    end.


(* -------------------------------------------------------------------------- *]
 When defining custom types, we slowly move into the new and exciting Coq
 territory. First we (re)define the familiar `option` type.
[* -------------------------------------------------------------------------- *)

Inductive option (A : Type) :=
    | None : option A
    | Some (x : A) : option A
    .

(* Why does this not work? *)
(* Example some_one := Some 1. *)

(* Let us look at a more 'raw' definition of `option`, where we explicitly
treat it as a function that returns a type. *)
(*
Inductive option : Type -> Type :=
    | None (A : Type) : option A 
    | Some (A : Type) : A -> option A
    .
*)

(* With this notation it is clearer that we must specify the type of the
constructor as well. *)
(* Example some_one := Some nat 1. *)


(* -------------------------------------------------------------------------- *]
 Supplying types directly is often cumbersome, so let us take a peek at some
 of the mechanisms that can help with that.
[* -------------------------------------------------------------------------- *)

(* We can use `_` instead of an argument and Coq will try to figure it out. *)
Example some_one := Some _ 1.

(* We can also mark arguments as implicit by using `{}` or `[]` (there is a
difference but we dont have a month to learn what the difference is). *)

Inductive opt {A : Type} :=
    | Non : opt
    | Som (x : A) : opt
    .

Example som_one := Som 1.

(* When we wish to directly supply type information, we do that by prefixing
 the type with `@`. *)

(* Coq is confused on what type of `option` this is... *)
(* Example non : opt := Non. *)

(* So we tell it. *)
Example non : @opt nat := Non.
Example also_non := @Non nat.


(* -------------------------------------------------------------------------- *]
 PRACTICE: (re)define a type for lists (use `Cons` and `Nil` for constructors).
 Then write an example (do not forget to supply types if explicit!).
[* -------------------------------------------------------------------------- *)

