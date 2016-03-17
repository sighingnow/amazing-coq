(* Code for Software Foundations, Chapter 6: Tactics: More Basic Tactics *)

Require Import Arith.
Require Import List.
Require Import Poly.

(* silly_ex *)

Theorem silly_ex :
  (forall n, Nat.even n = true -> Nat.odd (S n) = true) -> Nat.even 3 = true -> Nat.odd 4 = true.
Proof.
  intros h1 h2.
  apply h1.
  apply h2.
Qed.

(* apply_exercise1 *)

Theorem rev_exercise1 :
  forall l l' : list nat, l = rev l' -> l' = rev l.
Proof.
  intros l l'.
  (* Theorem rev_involutive :
    forall (X : Type) (l : list X), rev (rev l) = l. *)
  pattern l.
  rewrite <- rev_involutive.
  intros h1.
  rewrite h1.
  rewrite rev_involutive.
  reflexivity.
Qed.

(* apply_rewrite *)

(* The difference between "rewrite" and "apply":
  + apply: match current goal with argument's inclusion, generate new
    subgoals from it's hypotheses.
  + rewrite: rewrite from equation. *)

(* apply_with_exercise *)

Definition minus_two (n : nat) : nat :=
  match n with
    | O        => O
    | S O      => O
    | S (S n') => n'
  end.

Theorem trans_eq_exercise :
  forall n m o p, m = minus_two o -> n + p = m -> n + p = minus_two o.
Proof.
  intros n m o p h1 h2.
  rewrite h2.
  rewrite h1.
  reflexivity.
Qed.

(* inversion_exercise *)

Theorem inversion_ex1 :
  forall n m o : nat, n::m::nil = o::o::nil -> n::nil = m::nil.
Proof.
  intros n m o.
  inversion 1; reflexivity.
Qed.

Theorem inversion_ex2 :
  forall n m : nat, n::nil = m::nil -> n = m.
Proof.
  intros n m.
  inversion 1; reflexivity.
Qed.

Theorem inversion_ex3 :
  forall (X : Type) (x y z : X) (l j : list X), x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
Proof.
  intros X x y z l j.
  inversion 1.
  inversion 1.
  reflexivity.
Qed.

Theorem inversion_ex4 :
  forall n : nat, S n = O -> 2 + 2 = 5.
Proof.
  intros n.
  inversion 1.
Qed.

Theorem inversion_ex5 :
  forall n m : nat, false = true -> n::nil = m::nil.
Proof.
  intros n m.
  inversion 1.
Qed.

Theorem inversion_ex6 :
  forall (X : Type) (x y z : X) (l j : list X), x::y::l = nil -> y::l = z::j -> x = z.
Proof.
  intros X x y z l j.
  inversion 1.
Qed.

(* plus_n_n_injective *)

Theorem plus_n_n_injective :
  forall n m : nat, n + n = m + m -> n = m.
Proof.
  induction n, m.
  + simpl; reflexivity.
  + simpl; inversion 1.
  + simpl; inversion 1.
  + intros h1.
    simpl in h1.
    apply Nat.succ_inj in h1.
    pattern (n + S n) in h1; rewrite plus_comm in h1.
    pattern (m + S m) in h1; rewrite plus_comm in h1.
    simpl in h1.
    apply Nat.succ_inj in h1.
    apply eq_S.
    apply IHn.
    assumption.
Qed.

(* beq_nat_true *)

Theorem beq_nat_true :
  forall n m, beq_nat n m = true -> n = m.
Proof.
  induction n.
  + induction m.
    - simpl; reflexivity.
    - simpl; inversion 1.
  + induction m.
    - simpl; inversion 1.
    - intros h1.
      simpl in h1.
      apply IHn in h1.
      rewrite h1; reflexivity.
Qed.

(* gen_dep_practice *)

Theorem nth_error_after_last :
  forall (n : nat) (X : Type) (l : list X), length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  (* NOTE: PAY attention to the order of "generalize dependent" and "induction".
    WHY?
    If use "generalize" after "induction", the hypothesis can be proved under
    base condition still keeps it was after "induction", before "generalize".
    But in an opposite manner, the conclusion under base condition will contain
    the term introduced by "generalize". *)
  generalize dependent n.
  induction l.
  + intros n h1.
    rewrite <- h1.
    reflexivity.
  + intros n h1.
    simpl in h1.
    rewrite <- h1.
    simpl; apply IHl; reflexivity.
Qed.

(* app_length_cons *)

Theorem app_length_cons :
  forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n.
  induction l1.
  + simpl.
    intros; assumption.
  + simpl.
    intros h1.
    assert (length_app_succ : length (l1 ++ x :: l2) = S (length (l1 ++ l2))).
    - rewrite List.app_length.
      simpl.
      rewrite <- plus_n_Sm.
      rewrite List.app_length.
      reflexivity.
    - rewrite <- h1.
      rewrite length_app_succ.
      reflexivity.
Qed.

(* app_length_twice *)

Theorem app_length_twice :
  forall (X : Type) (n : nat) (l : list X), length l = n -> length (l ++ l) = n + n.
Proof.
  intros X n l h1.
  rewrite List.app_length.
  repeat rewrite h1.
  reflexivity.
Qed.

Lemma app_length :
  forall (X : Type) (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl; reflexivity.
  - simpl; rewrite IHl1; reflexivity.
Qed.

(* double induction *)
Theorem double_induction :
  forall (P : nat -> nat -> Prop),
    P O O -> (
      forall m, P m O -> P (S m) O) -> (
        forall n, P O n -> P O (S n)) -> (
          forall m n, P m n -> P (S m) (S n)) -> (
            forall m n, P m n).
Proof.
  intros P h1 h2 h3 h4.
  induction m.
  + induction n.
    - apply h1.
    - apply h3; apply IHn.
  + induction n.
    - apply h2; apply (IHm O).
    - apply h4.
      apply IHm.
Qed.

(* combine_split *)

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  induction l as [|(x, y) l'].
  + intros l1 l2 h1.
    simpl in h1.
    inversion h1.
    simpl; reflexivity.
  + simpl.
    destruct (split l') as [xs ys]. (* The KEY step! *)
    intros l1 l2 h1.
    inversion h1.
    simpl.
    rewrite IHl'; reflexivity.
Qed.

(* destruct_eqn_practice *)

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof.
  intros f b.

  assert(case_h1 : f true = true -> f false = true -> f (f (f b)) = f b).
  intros h1 h2.
  case b.
  repeat rewrite h1; reflexivity.
  rewrite h2; repeat rewrite h1; reflexivity.

  assert(case_h2 : f true = true -> f false = false -> f (f (f b)) = f b).
  intros h1 h2.
  case b.
  repeat rewrite h1; reflexivity.
  repeat rewrite h2; reflexivity.

  assert(case_h3 : f true = false -> f false = true -> f (f (f b)) = f b).
  intros h1 h2.
  case b.
  rewrite h1; rewrite h2; rewrite h1; reflexivity.
  rewrite h2; rewrite h1; rewrite h2; reflexivity.

  assert(case_h4 : f true = false -> f false = false -> f (f (f b)) = f b).
  intros h1 h2.
  case b.
  rewrite h1; repeat rewrite h2; reflexivity.
  repeat rewrite h2; reflexivity.

  destruct (f true).
  + destruct (f false).
    - apply case_h1; reflexivity.
    - apply case_h2; reflexivity.
  + destruct (f false).
    - apply case_h3; reflexivity.
    - apply case_h4; reflexivity.
Qed.

(* beq_nat_sym *)

Theorem beq_nat_sym :
  forall n m, beq_nat n m = beq_nat m n.
Proof.
  induction n, m.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + simpl; apply IHn.
Qed.

(* beq_nat_trans *)

Theorem beq_nat_trans :
  forall n m p, beq_nat n m = true -> beq_nat m p = true -> beq_nat n p = true.
Proof.
  induction n, m, p; try (simpl; reflexivity).
  + trivial.
  + trivial.
  + trivial.
  + inversion 1.
  + trivial.
  + simpl; apply IHn.
Qed.

(* split_combine *)

Theorem split_combine :
  forall (X : Type) (l1 l2 : list X), length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  induction l1, l2.
  + simpl; reflexivity.
  + simpl; inversion 1.
  + simpl; inversion 1.
  + simpl.
    intros h1.
    apply eq_add_S in h1.
    rewrite IHl1.
    - reflexivity.
    - assumption.
Qed.

(* filter_exercise *)

Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  induction l.
  + inversion 1.
  + intros lf h1.
    simpl in h1.
    (* destruct term "eqn:naming_intro_pattern" *)
    destruct (test a) as [] _eqn:h2.
    - inversion h1 as [eq_a_x].
      rewrite eq_a_x in h2.
      assumption.
    - apply (IHl lf); assumption.
Qed.

(* forall_exists_challenge *)

Fixpoint forallb {X : Type} (p : X -> bool) (l : list X) {struct l} : bool :=
  match l with
    | nil   => true
    | x::xs => andb (p x) (forallb p xs)
  end.

Fixpoint existsb {X : Type} (p : X -> bool) (l : list X) {struct l} : bool :=
  match l with
    | nil   => false
    | x::xs => if p x then true else existsb p xs
  end.

Definition existsb' {X : Type} (p : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (p x)) l).

Theorem existsb_eq :
  forall (X : Type) (p : X -> bool) (l : list X), existsb p l = existsb' p l.
Proof.
  intros X p l.
  unfold existsb'.
  induction l.
  + simpl; reflexivity.
  + simpl.
    destruct (p a) as [] eqn:pred_a.
    simpl; reflexivity.
    simpl; rewrite <- IHl; reflexivity.
Qed.


