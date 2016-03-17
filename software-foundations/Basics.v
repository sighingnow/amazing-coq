(* Code for Software Foundations, Chapter 2: Basics: Functional Programming in Coq *)

Require Import Arith.

(* nandb *)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  match b1, b2 with
    | true, true => false
    | _, _       => true
  end.

Example test_nandb1 :
  nandb true false = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_nandb2 :
  nandb false false = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_nandb3 :
  nandb false true = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_nandb4 :
  nandb true true = false.
Proof.
  simpl. reflexivity.
Qed.

(* andb3 *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _, _, _          => false
  end.

Example test_andb31:
  andb3 true true true = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_andb32:
  andb3 false true true = false.
Proof.
  simpl. reflexivity.
Qed.

Example test_andb33:
  andb3 true false true = false.
Proof.
  simpl. reflexivity.
Qed.

Example test_andb34:
  andb3 true true false = false.
Proof.
  simpl. reflexivity.
Qed.

(* factorial *)

Fixpoint factorial (n : nat) {struct n} : nat :=
  match n with
    | O    => 1
    | S n' => n * factorial n'
  end.

Example test_factorial1 :
  factorial 3 = 6.
Proof.
  simpl. reflexivity.
Qed.

Example test_factorial2 :
  factorial 5 = mult 10 12.
Proof.
  simpl. reflexivity.
Qed.

(* blt_nat *)

Fixpoint blt_nat (n m : nat) {struct n} : bool :=
  match n, m with
    | O, S _     => true
    | _, O       => false
    | S n', S m' => blt_nat n' m'
  end.

Example test_blt1 :
  blt_nat 2 2 = false.
Proof.
  simpl. reflexivity.
Qed.

Example test_blt2 :
  blt_nat 2 4 = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_blt3 :
  blt_nat 4 2 = false.
Proof.
  simpl. reflexivity.
Qed.

(* plus_id_exercise *)

Theorem plus_id_exercise :
  forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o h1 h2.
  rewrite h1.
  rewrite h2.
  reflexivity.
Qed.

(* mult_S_1 *)

Theorem mult_S_1 :
  forall n m : nat, m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m h1.
  rewrite h1.
  simpl; reflexivity.
Qed.

(* andb_true_elim2 *)

Theorem andb_true_elim2 :
  forall b c : bool, andb b c = true -> c = true.
Proof.
  intros b c h1.
  destruct c.
  + trivial.
  + elim h1.
    unfold andb.
    case b.
    - trivial.
    - trivial.
Qed.

(* zero_nbeq_plus_1 *)

Theorem zero_nbeq_plus_1 :
  forall n : nat, beq_nat O (n + 1) = false.
Proof.
  intros n.
  simpl.
  case n.
  + simpl. trivial.
  + simpl. trivial.
Qed.

(* boolean_functions *)

Theorem identity_fn_applied_twice :
  forall f : bool -> bool,  (
    forall x : bool, f x = x) ->
      forall b : bool, f (f b) = b.
Proof.
  intros f h1 b.
  repeat rewrite h1.
  reflexivity.
Qed.

(* andb_eq_orb *)

Theorem andb_eq_orb :
  forall b c : bool, andb b c = orb b c -> b = c.
Proof.
  intros b c h1.
  case b, c.
  - reflexivity.
  - unfold andb, orb in h1.
    rewrite h1; reflexivity.
  - unfold andb, orb in h1.
    rewrite h1; reflexivity.
  - reflexivity.
Qed.

(* binary *)

Inductive bin : Set :=
  | zero : bin
  | twice : bin -> bin
  | twice_succ : bin -> bin.

Fixpoint incr (x : bin) {struct x} : bin :=
  match x with
    | zero          => twice_succ zero
    | twice x'      => twice_succ x'
    | twice_succ x' => twice (incr x')
  end.

Fixpoint bin_to_nat (x : bin) {struct x} : nat :=
  match x with
    | zero          => O
    | twice x'      => let t := bin_to_nat x' in t + t
    | twice_succ x' => let t := bin_to_nat x' in S t + t
  end.

Example test_bin_incr :
  forall x : bin, S (bin_to_nat x) = bin_to_nat (incr x).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite <- IHx.
    apply eq_S. apply plus_n_Sm.
Qed.

(* decreasing *)

(* ackermann function is a good example. more information can be found at
  https://en.wikipedia.org/wiki/Ackermann_function .

  The oridinary recursive definition of ackermann function can't be
  implemented in Coq because of the restriction about termination.

    ackermann(m, n) :=
      n + 1                              -- m = 0
      ackermann(m-1, n)                  -- m > 0 and n = 0
      ackermann(m-1, ackermann(m, n-1))  -- m > 0 and n > 0

  While the non-recursive version is trivial.

    iterate(f)(0) = f(1)
    iterate(f)(n+1) = f(iter(f)(n))
    ackermann(0) = Succ
    ackermann(m + 1) = iterate(ackermann(m))
  *)

Definition ackermann (n m : nat) : nat :=
  let iterate := fix iterate_rec (fn : nat -> nat) (n : nat) {struct n} : nat :=
    match n with
      | O => fn 1
      | S n' => fn (iterate_rec fn n')
    end
  in
  let ackermann_impl := fix ackermann_rec (n : nat) {struct n} : nat -> nat :=
    match n with
      | O    => S
      | S n' => fun fx => iterate (ackermann_rec n') fx
    end
  in ackermann_impl n m.

