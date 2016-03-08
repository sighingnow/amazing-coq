(* Solution for exercieses in Tsinghua Coq Summber School.
  Exercise for leture 1: Programming with Coq by Yves Bertot. *)
Section Exercise_1_Work.

Require Import List.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import ZArith.

(* Define a function that takes a tuple of numbers (a,b) and returns
  the sum of the squares of both numbers. *)

Definition tuple_sum (t : nat * nat) : nat :=
  let (x, y) := t
  in x*x + y*y.

(* Define a function that computes the sum of all squares between 1 and n,
  as a natural number.  Use the Fixpoint approach as described in the slides. *)

Fixpoint square_sum (n : nat) : nat :=
  match n with
    | O   => 0
    | S p => (n * n) + square_sum p
  end.

(* Write a function that maps any positive integer n to the list 1 ... n *)
(* Use the iter function shown in the slides. *)

Fixpoint nat_list (n : nat) : list nat :=
  match n with
    | O   => nil
    | S p => n::(nat_list p)
  end.

(* Write a function that maps any n and any list a_1::...::a_p::nil
  to the list (n*a_1::...n*a_p::nil) *)

Fixpoint mult_list (n : nat) (xs : list nat) : list nat :=
  match xs with
    | nil         => nil
    | cons x rest => cons (n*x) (mult_list n rest)
  end.

(* Write a function that maps any n and any list l and returns the boolean
  value that indicates whether n is in l.
  Use the function fold_right given in the slides and a function Zeq_bool
  to compare to integers *)

Fixpoint nat_eq_bool_local (n m : nat) : bool :=
  match n, m with
    | O, O     => true
    | O, S _   => false
    | S _, O   => false
    | S a, S b => nat_eq_bool_local a b
  end.

(* NOTE that `nat_eq_bool` from Coq.Arith.Bool_nat and the `beq_nat` (or `Nat.eqb`)
  have the different meaning as well as types ! *)
Definition nat_contains (n : nat) (xs : list nat) : bool :=
  fold_right
    (fun x res => if beq_nat n x then true else res)
    false xs.

Open Scope Z_scope.

Definition Z_contains (n : Z) (xs : list Z) : bool :=
  fold_right
    (fun x res =>
      if (Zeq_bool n x)
        then true
        else res)
    false xs.

(* Write a function that checks whether n divides p, assuming n and p
   are both positive.  Here's a plan:
   build the list n::2*n::...::p*n::nil,
   check whether p is in this list. *)

Open Scope nat_scope.

Definition nat_divides (n p : nat) : bool :=
  nat_contains p (mult_list n (nat_list p)).

(* test nat_divides. *)
(* Eval compute in nat_divides 2 10. (* true *)
Eval compute in nat_divides 3 10. (* false *)
Eval compute in nat_divides 5 10. (* true *) *)

(* Write a function that checks whether n is prime. *)

Fixpoint nat_ge_bool_local (n m : nat) : bool :=
  match n, m with
    | O, O     => true
    | O, S _   => false
    | S _, O   => true
    | S a, S b => nat_ge_bool_local a b
  end.

Fixpoint nat_list_from_k (n k : nat) : list nat :=
  match n with
    | O   => nil
    | S p =>
      if (nat_ge_bool_local n k)
        then n::nat_list_from_k p k
        else nil
  end.

Definition prime (n : nat) : bool :=
  match n with
    | O   => false
    | 1   => false
    | 2   => true
    | S p => fold_right
      (fun x res =>
        if (nat_divides x n)
          then false
          else res)
      true (nat_list_from_k p 2)
  end.

(* test prime. *)
(* Eval compute in prime 1. (* false *)
Eval compute in prime 2. (* true *)
Eval compute in prime 3. (* true *)
Eval compute in prime 4. (* false *)
Eval compute in prime 5. (* true *)
Eval compute in prime 6. (* false *)
Eval compute in prime 7. (* true *)
Eval compute in prime 8. (* false *)
Eval compute in prime 9. (* false *)
Eval compute in prime 10. (* false *)
Eval compute in prime 11. (* true *) *)

(* Define div and mod for natural number in Coq.
  Reference Coq.Numbers.Natural.Peano.NPeano. *)

Fixpoint nat_divmod (a b quotient remainder : nat) : nat * nat :=
  match a with
    | O   => (quotient, remainder)
    | S t =>
      match remainder with
        | O   => nat_divmod t b (S quotient) b
        | S r => nat_divmod t b quotient r
      end
  end.

Definition nat_div (a b : nat) : nat :=
  match b with
    | O   => b
    | S t => fst (nat_divmod a t 0 t)
  end.

Definition nat_mod (a b : nat) : nat :=
  match b with
    | O   => b
    | S t => t - snd (nat_divmod a t 0 t)
  end.

(* Eval compute in nat_div 10 3.
Eval compute in nat_mod 10 3. *)

End Exercise_1_Work.
