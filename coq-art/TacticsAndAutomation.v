(* Code for Coq'Art, Chapter 7: Tactics and Automation. *)

Section TacticsAndAutomation.

Require Import Arith.
Require Import ZArith.
Require Import List.

(* Examples *)
Section Examples.

Theorem le_plus_minus' :
  forall n m : nat, m <= n -> n = m + (n - m).
Proof.
  intros n m.
  induction n.
    + intros h1.
      rewrite <- le_n_0_eq  with (1 := h1).
      simpl; trivial.
    + auto with arith.
Qed.

Theorem simpl_pattern_example :
  3 * 3 + 3 * 3 = 18.
Proof.
  simpl; trivial.
Qed.

Theorem lazy_example :
  forall n : nat, (S n) + O = S n.
Proof.
  intros n.
  rewrite <- plus_n_O; trivial.
Qed.

Section CombinatoryLogic.

Variables
  (CL : Set)
  (App : CL -> CL -> CL)
  (S : CL)
  (K : CL).

Hypotheses
  (S_rule :
    forall A B C : CL, App (App (App S A) B) C = App (App A C) (App B C))
  (K_rule :
    forall A B : CL, App (App K A) B = A).

Hint Rewrite S_rule K_rule : CL_rules.

Theorem obtain_I :
  forall A : CL, App (App (App S K) K) A = A.
Proof.
  intros A.
  autorewrite with CL_rules; trivial.
Qed.

End CombinatoryLogic.

Theorem example_for_subst :
  forall a b c d : nat, a = b + c -> c = 1 -> a + b = d -> 2 * a = d + c.
Proof.
  intros a b c d h1 h2 h3.
  subst a.
  subst d.
  subst c.
  unfold mult.
  rewrite plus_0_r.
  rewrite <- plus_assoc_reverse.
  trivial.
Qed.

Section ProofWithTauto.

(* Some logical formulas that are solved by "tauto" and not by "auto". *)

Lemma disjunction_intro_l :
  forall A B : Prop, A /\ B -> A.
Proof.
  intros A B.
  tauto. (* "intros h1; apply h1." *)
Qed.

Lemma contradiction :
  forall A B : Prop, A /\ ~ A -> B.
Proof.
  intros A B [h1 h2].
  elim h2; apply h1.
Qed.

Theorem example_intuition :
  forall n p q : nat, n <= p \/ n <= q -> n <= p \/ n <= S q.
Proof.
  intros n p q.
  intuition auto.
Qed.

End ProofWithTauto.

Ltac contrapose H :=
  match goal with
    | [id : (~ _) |- (~ _)] => intros H; apply id
  end.

Theorem example_constrapose :
  forall x y : nat, x <> y -> x <= y -> ~ y <= x.
Proof.
  intros x y h1 h2.
  (* "intros h3.
    auto with arith." *)
  contrapose h3.
  auto with arith.
Qed.
Print example_constrapose.

Ltac auto_after tac :=
  try (tac; auto; fail).
Ltac auto_clear h :=
  try (clear h; auto; fail).
Ltac clear_all :=
  match goal with
    | [id : _ |- _] => clear id; clear_all
    | [|- _]        => idtac
  end.

Ltac simpl_on e :=
  let v := eval simpl in e
  in match goal with
    | [|- context [e]] => replace e with v; [idtac | auto]
  end.

Theorem simpl_on_example :
  forall n : nat, exists m : nat, (1 + n) + 4 * (1 + n) = 5 * (S m).
Proof.
  intros n.
  simpl_on (1+n).
  pattern (S n) at 1.
  rewrite <- mult_1_l with (n := (S n)).
  rewrite <- mult_plus_distr_r with (n := 1) (m := 4) (p := (S n)).
  exists n. trivial.
Qed.

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 7.1 Some lemmas about divisibility. *)

Section Primes.

Definition divides (n m : nat) :=
  exists p : nat, p * n = m.

Lemma divides_O:
  forall n : nat, divides n O.
Proof.
  unfold divides; intros n.
  exists O. simpl. reflexivity.
Qed.

Lemma divides_plus :
  forall n m : nat, divides n m -> divides n (n + m).
Proof.
  unfold divides; intros n m.
  intros h1.
  destruct h1.
  exists (S x).
  rewrite mult_succ_l.
  (* "omega." *)
  rewrite <- H.
  rewrite plus_comm.
  trivial.
Qed.

Lemma not_divides_plus :
  forall n m : nat, ~ divides n m -> ~ divides n (n + m).
Proof.
  unfold divides; intros n m.
  intros h1 h2.
  elim h1.
  destruct h2.
  exists (x - 1).
  rewrite mult_minus_distr_r.
  rewrite H.
  omega.
Qed.
Print not_divides_plus.

Lemma not_zero_lt_zero :
  O < O -> False.
Proof.
  omega.
Qed.

Lemma not_succ_mult_lt :
  forall x n : nat, S x * n < n -> False.
Proof.
  intros x n h1; simpl mult in h1.
  absurd (n + x * n < n).
    + apply le_not_lt. apply le_plus_l.
    + apply h1.
Qed.

Lemma not_divides_lt :
  forall n m : nat, O < m -> m < n -> ~ divides n m.
Proof.
  unfold divides; intros n m.
  intros h1 h2 h3.
  destruct h3.
  rewrite <- H in h1, h2.

  induction x.
    + simpl mult in h1.
      apply not_zero_lt_zero; apply h1.
    + apply (not_succ_mult_lt x n); apply h2.
Qed.

Lemma not_lt_2_divides :
  forall n m : nat, n <> 1 -> n < 2 -> O < m -> ~ divides n m.
Proof.
  unfold divides; unfold not.
  intros n m h1 h2 h3 h4.
  destruct h4.
  induction n; omega.
Qed.
Print not_lt_2_divides.

Lemma le_plus_minus :
  forall n m : nat, le n m -> m = n + (m - n).
Proof.
  intros. omega.
Qed.

Lemma lt_lt_or_eq :
  forall n m : nat, n < S m -> n < m \/ n = m.
Proof.
  intros n m. omega.
Qed.

End Primes.

(* Exercise 7.2 Rewriting with exceptions. *)

Open Scope Z_scope.

Theorem z_positive_example :
  forall x, Zpos (xO (xI x)) = 4 * (Zpos x) + 2.
Proof.
  simpl.
  trivial.
Qed.

End Exercises.

End TacticsAndAutomation.
