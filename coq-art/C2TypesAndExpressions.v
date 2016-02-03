(* Code for Coq Art, Chapter 2: Types and Expressions. *)

Section TypesAndExpressions.

Require Import List.
Require Import ZArith.
Require Import Bool.
Require Import Relations.

(* Examples *)
Section Examples.

(* Define specification *)
Definition Z_bin : Set :=
   Z -> Z -> Z.

(* Declare specification *)
Variable A B : Set. (* Variable can declares an arbitrary specification. *)
Let Z_bin' : Set :=
  Z -> Z -> Z. (* Define "abstract" functions working on this specifications. *)

(* Realize specification *)
Definition Z_dist : Z_bin :=
  fun a b: Z => let d := (a-b)%Z in (d*d)%Z.

Let Z_dist' : Z_bin' :=
  fun a b: Z => let d := (a-b)%Z in (d*d)%Z.

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 2.2 *)
Check (fun a b c: Z => (b*b-4*a*c) % Z).

(* Exercise 2.3 *)
Check (fun (f g: nat -> nat) (n: nat) => g (f n)).

(* Exercise 2.5 *)
Definition sum_five_integers :=
  fun a b c d e: Z => (a + b + c + d + e) % Z.

(* Exercise 2.6
  Those local variables that are used in a global definition
  are added as abstractions around this global definition.
  But, error may occurred.*)
Section SumFiveIntegers.
Variable a b c d e : Z.
Definition _sum_five_integers := (a + b + c + d + e) % Z.
End SumFiveIntegers.

Definition sum_five_integers' := _sum_five_integers.

(* Exercise 2.7 *)
Definition fn := fun x: Z => (2*x*x+3*x+3) % Z.

Eval compute in (fn 2).
Eval compute in (fn 3).
Eval compute in (fn 5).
Eval compute in (fn (-2)).
Eval compute in (fn (-3)).
Eval compute in (fn (-5)).

End Exercises.

End TypesAndExpressions.
