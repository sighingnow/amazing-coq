(* Code for Coq Art, Chapter 1: A Brief Overview *)

Section ABriefOverview.

Require Import List.
Require Import ZArith.
Require Import Bool.
Require Import Relations.

(* Examples *)
Section Examples.

Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
  | sorted_nil       :
    sorted nil
  | sorted_singleton :
    forall a: Z, sorted (a :: nil)
  | sorted_all       :
    forall (a b: Z) (l: list Z),
      (a <= b) -> sorted (b :: l) -> sorted (a :: b :: l).

End Examples.

(* Exercises. *)
Section Exercises.

End Exercises.

End ABriefOverview.


