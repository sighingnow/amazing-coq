(* Code for Coq Art, Chapter 5: Everyday Logic. *)

Section EverydayLogic.

Require Import Arith.
Require Import ZArith.
Require Import List.

(* Examples *)
Section Examples.

Definition lt (n p : nat) : Prop :=
  S n <= p.

Theorem conv_example :
  forall n : nat, 7 * 5 < n -> 6 * 6 <= n.
(* The two formulas are convertible:
  + a delta-reduction on lt,
  + two beta-reductions, (function application), get "S (7*5) <= n".
  + then, convert "S (7*5) <= n" and "6*6 <= n" both to 36<=n.
  After "intros n h1", the convertiblity of the goal and hypothesis h1 make the
  tactic "apply h1" succeed.*)
Proof.
  intros n h1.
  apply h1.
Qed.
Print conv_example.

(* Polymorphic version of "implication transitivity". *)
Theorem imp_trans_poly :
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R h1 h2 h3.
  apply h2; apply h1; apply h3.
Qed.
Implicit Arguments imp_trans_poly [P Q R].
Print imp_trans_poly.
Print le_S.
Check (imp_trans_poly _ _ _ (le_S 0 1) (le_S 0 2)).

Definition neutral_left (A : Set) (op : A -> A -> A) (e : A) :=
  forall x : A, op e x = x.
Theorem neutral_left_one : neutral_left Z Zmult 1%Z.
Proof.
  intros value.
  (* TODO: how to prove it ? *)
Admitted.
Print neutral_left_one.

Theorem ls_SS :
  forall i : nat, i <= S (S i).
Proof.
  intros i.
  apply le_S; apply le_S; apply le_n.
Qed.

Theorem imp_dist_all :
  forall (A : Type) (P Q : A -> Prop), (
    forall x : A, P x -> Q x) -> (
      forall y : A, P y) ->
        forall z : A, Q z.
Proof.
  intros TA P Q h1 h2.
  intros value.
  apply h1; apply h2.
Qed.
Print imp_dist_all.

(* TODO: How to prove these three lemmas ? *)

Lemma le_trans :
  forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p h1 h2.
Admitted.

Lemma mult_le_compat_l :
  forall n m p : nat, n <= m -> p * n <= p * m.
Proof.
Admitted.

Lemma mult_le_compat_r :
  forall n m p : nat, n <= m -> n * p <= m * p.
Proof.
Admitted.

(* Use apply...at... or eapply... . *)

Theorem le_mult_mult :
  forall a b c d : nat, a <= c -> b <= d -> a * b <= c * d.
Proof.
  intros a b c d h1 h2.
  (* apply ... with ... to build explicit mapping. *)
  apply le_trans with (m := c * b); [
      apply mult_le_compat_r; apply h1
    | apply mult_le_compat_l; apply h2
  ].
Qed.
Print le_mult_mult.

Theorem le_mult_mult' :
  forall a b c d : nat, a <= c -> b <= d -> a * b <= c * d.
Proof.
  intros a b c d h1 h2.
  eapply le_trans.
  apply mult_le_compat_l.
  apply h2.
  apply mult_le_compat_r.
  apply h1.
Qed.

Lemma le_0_mult :
  forall n p : nat, 0 * n <= 0 * p.
Proof.
  intros n p.
  apply le_n.
Qed.

Lemma lt_8_9 : 8 < 9.
Proof.
  (* Here, "unfold lt" is not needed in Coq 8.5. *)
  unfold lt.
  apply le_n.
Qed.

Open Scope Z_scope.

Definition Zsquare_diff (x y : Z) := x * x - y * y.

Theorem unfold_example :
  forall x y : Z, x * x = y * y -> Zsquare_diff x y * Zsquare_diff (x + y) (x * y) = 0.
Proof.
  intros x y h1.
  unfold Zsquare_diff at 1.
Admitted.
Print unfold_example.

Open Scope nat_scope.

Theorem lt_S :
  forall n p : nat, n < p -> n < S p.
Proof.
  intros n p h1.
  apply le_S.
  trivial. (* TODO: "trivial" tatic ?*)
Qed.

(* Logic Connectives. *)
Section LogicConnectives.

(* If a logic system is inconsistant, any propositions can be proved in via
  eliminating the contradiction (using the "elim" tactic).
  The "False" proposition represents the absolute contradiction. There's no
  introduction rule for this proposition, it's only possible to prove it in
  a context that already contains a contradiction. *)
Section InconsistantExample.

Hypothesis false : False.

Check False_ind.
Print False_ind.

(* The "elim" tactic:
  usage: "elim t".
  + if "t" is a term with type "False", then the current goal was solved immediately.
  + or else, if "t" is a negation (with form "~ x"), "elim t" ("elim ~ x") will solve
    the current goal with creating a new subgoal "x". then, if "x" can be proved,
    the original proposition can be proved.
    NOTE: if "t" doesn't have a "~ ", CAN NOT apply the "elim" tactic on it. *)

Lemma false_ex1 : 220 = 284.
Proof.
  apply False_ind.
  exact false.
Qed.

Lemma false_ex2 : 220 = 284.
Proof.
  elim false.
Qed.

Theorem absurd :
  forall P Q : Prop, P -> ~ P -> Q.
Proof.
  intros P Q h1 h2.
  elim h2. (* "h2 = ~ p", so, this step will solve "q" and introduce a subgoal "p". *)
  assumption.
Qed.
Print absurd.

(* Under the intuitionism logic, the goal "double_neg_l" can't be proved, however
  the goal "double_neg_r" can be proved trivially. *)

(* Theorem double_neg_l :
  forall P : Prop, ~ ~ P -> P. *)

Theorem double_neg_r :
  forall P : Prop, P -> ~ ~ P.
Proof.
  intros P hp.
  (* Here, we want to prove "~ ~ p", the "intros hp_neg" will introduce a hypothesis
    "~ p" and a subgoal "False". The tiatics "elim" the "~ p" (in the context), and
    "apply p" will lead to a contradiction. (NOTE: CAN NOT "elim p"). *)
  intros hp_neg.
  elim hp_neg; apply hp. (* another solution: "apply hg_neg; apply hp.". *)
Qed.
Print False.
Print double_neg_r.

Theorem contrad_example :
  forall P Q : Prop, ((P -> Q) -> P) -> (~ P -> P).
Proof.
  intros P Q.
  intros h1 h2.
  apply h1.
  intros h3.
  (* NOTE now we get a contradiction. *)
  elim h2; assumption.
Qed.

End InconsistantExample.

(* The theorem "double_neg_r" is a simple instance of the modus ponens rule.
  "modus_ponens p False" equals to "P -> (P -> False) -> False".
  After "unfold not", the goal "P -> ~ ~ P" becomes "P -> (P -> False) -> False". *)

Theorem modus_ponens :
  forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q h1 h2.
  apply h2; assumption.
Qed.
Print modus_ponens.

Theorem double_neg_r' :
  forall P : Prop, P -> ~ ~ P.
Proof.
  intros P.
  unfold not.
  exact (modus_ponens P False).
Qed.
Print double_neg_r'.

(* The contraposition is a direct application of "implication transitivity".
  After "unfold not.", the goal becomes "(a -> b) -> (b -> False) -> a -> False". *)

Theorem contrap :
  forall A B : Prop, (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B.
  unfold not.
  apply imp_trans_poly.
Qed.

Theorem split_example :
  forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  intros P Q h1 h2.
  split; [assumption | assumption].
Qed.

Theorem conj3 :
  forall P Q R : Prop, P -> Q -> R -> P /\ Q /\ R.
Proof.
  intros P Q R h1 h2 h3.
  repeat split; assumption.
Qed.

Theorem disj4_3 :
  forall P Q R S : Prop, R -> P \/ Q \/ R \/ S.
Proof.
  intros P Q R S h1.
  right; right; left; assumption.
Qed.

Theorem and_commutes :
  forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B h1.
  split; apply h1.
Qed.

Theorem and_commutes' :
  forall A B : Prop, A /\ B -> B /\ A.
Proof.
  intros A B h1.
  elim h1.
  (* "split" = "intros; apply conj." *)
  split; assumption.
Qed.

Theorem or_commutes :
  forall A B : Prop, A \/ B -> B \/ A.
Proof.
  intros A B.
  intros [h1 | h2]; [right | left]; assumption.
Qed.

End LogicConnectives.

Theorem ex_imp_ex :
  forall (A : Type) (P Q : A -> Prop), (ex P) -> (
    forall x : A, P x -> Q x) -> (ex Q).
Proof.
  intros TA P Q h1 h2.
  elim h1.
  intros x h3.
  exists x.
  apply h2; assumption.
Qed.
Print ex_imp_ex.

Theorem eq_36 : 6 * 6 = 4 * 9.
Proof.
  apply refl_equal.
Qed.

Theorem eq_36' : 6 * 6 = 4 * 9.
Proof.
  reflexivity.
Qed.

Open Scope Z_scope.

Theorem diff_of_squares :
  forall a b : Z, (a+b) * (a-b) = a*a - b*b.
Proof.
  intros.
  ring. (* defined in "ZArithRing" *)
Qed.

Theorem symbol_equal :
  forall (A : Type) (a b : A), a = b -> b = a.
Proof.
  intros TA a b.
  intros h1.
  rewrite h1. (* also can be done by "rewrite <- h1". *)
  trivial.
Qed.

Theorem Zmult_distr_example_l :
  forall n x : Z, n * x + x = (n + 1) * x.
Proof.
  intros n x.
  rewrite Zmult_plus_distr_l.
  rewrite Zmult_1_l.
  trivial.
Qed.

Theorem Zmult_distr_example_r :
  forall n x : Z, n * x + x = x * (n + 1).
Proof.
  intros n x.
  rewrite Zmult_plus_distr_r.
  rewrite Zmult_1_r.
  rewrite Z.mul_comm.
  trivial.
Qed.

Theorem regroup :
  forall x : Z, x + x + x + x + x = 5 * x.
Proof.
  intros x.
  pattern x at 1 2 3 4 5.
  rewrite <- Zmult_1_l.
  repeat rewrite <- Zmult_plus_distr_l.
  trivial.
Qed.

Open Scope nat_scope.

Lemma le_lt_S_eq :
  forall n p : nat, n <= p -> p < S n -> n = p.
Proof.
  intros n p.
  omega.
Qed.

Theorem cond_rewrite_example :
  forall n : nat, 8 < n + 6 -> 3 + n < 6 -> n * n = n + n.
Proof.
  intros n h1 h2.
  rewrite <- (le_lt_S_eq 2 n);
    [ idtac
    | apply plus_le_reg_l with (n := 2) (m := n) (p := 6)
    | apply plus_lt_reg_l with (n := n) (m := 3) (p := 3)
    ].
  (* TODO I think this proof (as follows) is wrong !!!
    From the last two subgoals we know that "n" must equal to "2",
    but it contradicts with the hypotheses "h1" and "h2". *)
(* Proof.
 intros n  H H0.
 rewrite <- (le_lt_S_eq 2 n).
 simpl; auto.
 apply  plus_le_reg_l with (p := 6). 
 rewrite plus_comm in H; simpl; auto with arith.
 apply   plus_lt_reg_l with (p:= 3). auto with arith.
Qed. *)
Admitted.

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 5.1 Polymorphic minimal propositional logic. *)

Lemma id_P :
  forall P : Prop, P -> P.
Proof.
  intros P h1.
  apply h1.
Qed.
Print id_P.

Lemma id_PP :
  forall P : Prop, (P -> P) -> (P -> P).
Proof.
  intros P h1.
  apply h1.
Qed.

Lemma imp_trans :
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R h1 h2 h3.
  apply h2.
  apply h1.
  apply h3.
Qed.

Lemma imp_perm :
  forall P Q R : Prop, (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros P Q R h1 h2 h3.
  apply h1.
  apply h3.
  apply h2.
Qed.

Lemma ignore_Q :
  forall P Q R : Prop, (P -> R) -> P -> Q -> R.
Proof.
  intros P Q R h1 h2 h3.
  apply h1; apply h2.
Qed.

Lemma delta_imp :
  forall P Q R : Prop, (P -> P -> Q) -> P -> Q.
Proof.
  intros P Q R h1 h2.
  apply h1; [apply h2 | apply h2].
Qed.

Lemma delta_impR :
  forall P Q R : Prop, (P -> Q) -> (P -> P -> Q).
Proof.
  intros P Q R h1 h2.
  apply h1.
Qed.

Lemma diamond :
  forall P Q R T : Prop, (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros P Q R T h1 h2 h3 h4.
  apply h3; [apply h1; apply h4 | apply h2; apply h4].
Qed.
Print diamond.

Lemma weak_peirce :
  forall P Q R : Prop, ((((P -> Q) -> P) -> P) -> Q) -> Q.
(* Perice formula: ((P -> Q) -> P) -> P. can't be proved by Coq (Calculus of
  Constructions), it uses normalization properties in typed lambda-calculi. *)
Proof.
  intros P Q R h1.
  apply h1.
  intros h2.
  apply h2.
  intros h3.
  apply h1.
  intros h4.
  apply h3.
Qed.
Print weak_peirce.

(* Exercise 5.2 Some proofs in predicate calculus. *)

Theorem all_perm' :
  forall (A : Type) (P : A -> A -> Prop), (
    forall (x y : A), P x y) ->
      forall (x y : A), P y x.
Proof.
  intros TA P h1 v1 v2.
  apply h1.
Qed.
Print all_perm'.

Theorem resolution :
  forall (A : Type) (P Q R S : A -> Prop), (
    forall (a : A), Q a -> R a -> S a) -> (
      forall (b : A), P b -> Q b) -> (
        forall (c : A), P c -> R c -> S c).
Proof.
  intros TA P Q R S h1 h2.
  intros v1.
  intros v2 v3.
  apply h1; [apply h2; apply v2 | apply v3].
Qed.
Print resolution.

(* Exercise 5.3 On Negation, prove WITHOUT "False_ind". *)

Lemma lem1 : ~ False.
Proof.
  (* If item "t" can imply "False", then "~ t" will be proved. *)
  intros h1.
  apply h1.
Qed.

Lemma lem2 :
  forall P : Prop, ~ ~ ~ P -> ~ P.
Proof.
  intros P.
  intros h1 h2.
  apply h1.
  intros h3.
  elim h3; apply h2.
Qed.

Lemma lem3 :
  forall P Q : Prop, ~ ~ ~ P -> P -> Q.
Proof.
  intros P Q h1 h2.
  elim h1.
  intros h3.
  elim h3; apply h2.
Qed.

Lemma lem4 :
  forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P.
Proof.
  intros P Q h1 h2 h3.
  (* Assume "q" and prove it, the get contradiction. *)
  elim h2.
  apply h1; assumption.
Qed.

Lemma lem4' :
  forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P.
Proof.
  intros P Q.
  unfold not.
  apply imp_trans_poly.
Qed.

Lemma lem5 :
  forall P Q R : Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
Proof.
  intros P Q R.
  intros h1 h2 value.
  elim (h2 value); apply h1; assumption.
Qed.
Print lem5.

(* Exercise 5.4 Some bad inference rules. *)

(** TODO **)

(* Exercise 5.5 Introducing equality and disjunction. *)

Theorem refl_eq :
  forall (A : Set) (a b c d : A), a = c \/ b = c \/ c = c \/ d = c.
Proof.
  intros TA a b c d.
  right; right; left.
  (* The equal relation is reflexive. *)
  apply refl_equal. (* Here the tactic "reflexivity" also work. *)
Qed.

(* Exercise 5.6 Intuitionistic Propositional Logic. *)

Theorem and_assoc :
  forall A B C : Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  (* Bind variable in conjunctive pattern with hypothesis using "intros". *)
  intros A B C [h1 [h2 h3]].
  repeat split; assumption.
Qed.

Theorem and_imp_dist :
  forall A B C D : Prop, (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
  intros A B C D [h1 h2] [h3 h4].
  split; [apply h1 | apply h2]; assumption.
Qed.

Theorem not_contrad :
  forall A : Prop, ~ (A /\ ~ A).
Proof.
  intros A [h1 h2].
  apply h2; apply h1.
Qed.
Print not_contrad.

Theorem or_assoc :
  forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C.
  intros [h1 | [h2 | h3]].
  left; left; assumption.
  left; right; assumption.
  right; assumption.
Qed.

Theorem double_neg_true :
  forall A : Prop, ~ ~ (A \/ ~ A).
Proof.
  intros A h1.
  elim h1.
  right; intros h2.
  elim h1.
  left; assumption.
Qed.
Print double_neg_true.

(* TODO There's another way to finish this proof. Why this implimentation
  successes ? What's the detailed type of "h1" ? *)
Theorem double_neg_true' :
  forall A : Prop, ~ ~ (A \/ ~ A).
Proof.
  intros A h1.
  exact (h1 (or_intror (fun value : A => h1 (or_introl value)))).
Qed.
Print double_neg_true'.

Theorem or_and_not :
  forall A B : Prop, (A \/ B) /\ ~ A -> B.
Proof.
  intros A B [[h1 | h2] h3].
  elim h3; apply h1.
  assumption.
Qed.

(* Exercise 5.7 Five characterizations of classical logic. *)

Definition peirce :=
  forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition classic :=
  forall P : Prop, ~ ~ P -> P.
Definition excluded_middle :=
  forall P : Prop, P \/ ~ P.
Definition de_morgan_not_and_not :=
  forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q.
Definition implies_to_or :=
  forall P Q : Prop, (P -> Q) -> (~ P \/ Q).

Goal peirce <-> classic.
Proof.
  unfold peirce; unfold classic; unfold not.

  split.

  intros hypo_perice.
  intros P h2.
  apply (hypo_perice P False).
  intros h3; elim h2; assumption.

  intros hypo_classic.
  intros P Q h1.
  apply hypo_classic; intros h2.
  apply h2.
  apply h1.
  intros h3.
  apply hypo_classic;
  intros h4.
  apply h2; apply h3.
Qed.

Goal peirce <-> excluded_middle.
Proof.
  unfold peirce; unfold excluded_middle.

  split.

  (* NOTE important skill !!!. *)
  intros hypo_perice P.
  apply (hypo_perice (P \/ ~ P) False).
  intros h1.
  right; intros h2.
  elim h1.
  left; assumption.

  intros hypo_em P Q h1.
  elim (hypo_em P);
    [ intros h2
    | intros h2; apply h1; intros h3; elim h2
    ];
    assumption.
Qed.

Goal peirce <-> de_morgan_not_and_not.
Proof.
  unfold peirce; unfold de_morgan_not_and_not.

  split.
  (* TODO *)
Admitted.

Goal peirce <-> implies_to_or.
Proof.
  (* TODO *)
Admitted.

Goal classic <-> excluded_middle.
Proof.
  unfold classic; unfold excluded_middle; unfold not.

  split.

  intros hypo_classic P.
  (* NOTE important skill !!!. *)
  apply hypo_classic.
  intros h2; apply h2.
  right; intros h3.
  elim h2.
  left; assumption.

  intros hypo_em P;
  elim (hypo_em P); intros h1 h2; [idtac | elim h2]; apply h1.
Qed.

Goal classic <-> de_morgan_not_and_not.
Proof.
  unfold classic; unfold de_morgan_not_and_not.

  split.

  intros hypo_classic P Q.
  intros h1.
  apply (hypo_classic (P \/ Q)).
  intros h2.
  apply h1; split; intros h3; elim h2; [left | right]; apply h3.

  intros hypo_de_morgan P.
  intros h1.
  elim (hypo_de_morgan P (~ P));
    [ trivial
    | intros h2; elim h1; assumption
    | intros h2; elim h2; intros h3 h4; elim h4; assumption
    ].
Qed.

Goal classic <-> implies_to_or.
Proof.
  (* TODO *)
Admitted.

Goal excluded_middle <-> de_morgan_not_and_not.
Proof.
  (* TODO *)
Admitted.

Goal excluded_middle <-> implies_to_or.
Proof.
  unfold excluded_middle; unfold implies_to_or.

  split.

  unfold not.
  intros hypo_em P Q.
  intros h1.
  elim (hypo_em P);
    [ intros h2; right; apply h1; apply h2
    | intros h3; left; apply h3
    ].

  intros hypo_impl P.
  elim (hypo_impl P P); intros;
    [ right
    | left
    | idtac];
    assumption.
Qed.

Goal de_morgan_not_and_not <-> implies_to_or.
Proof.
  (* TODO *)
Admitted.

(* Exercise 5.8 *)

(** The usage of:
  + "repeat idtac" keep a goal as it was.
  + "repeat fail" ? (* TODO *) **)

(* Exercise 5.9 On the existential quantifier. *)

Theorem ex_or_l :
  forall (A : Type) (P Q : A -> Prop), (
    exists x : A, P x \/ Q x) -> ex P \/ ex Q.
Proof.
  intros TA P Q h1.
  elim h1.
  intros x h2.
  elim h2; [left | right]; exists x; assumption.
Qed.

Theorem ex_or_r :
  forall (A : Type) (P Q : A -> Prop), (ex P \/ ex Q) -> (
    exists x : A, P x \/ Q x).
Proof.
  intros TA P Q.
  intros [h1 | h2];
    [ elim h1
    | elim h2
    ];
    intros; exists x;
    [ left
    | right
    ]; assumption.
Qed.

Theorem ex_universal_relation :
  forall (A : Type) (P Q : A -> Prop), (
    exists x : A,
      forall R : A -> Prop, R x) -> 2 = 3.
Proof.
  intros TA P Q.
  intros h1.
  elim h1.
  intros x hr1.
  (* Construct  a relation that maps all elements with type "TA" to "False".
    TODO The question if that how this approach works and how to construct a solution
    for general problem ? *)
  elim (hr1 (fun e : TA => False)).
Qed.

Theorem forall_not_ex :
  forall (A : Type) (P Q : A -> Prop), (
    forall x : A, P x) -> ~ (
      exists y : A, ~ P y).
Proof.
  intros TA P Q.
  intros h1 h2.
  elim h2.
  intros x h3.
  elim h3; apply h1.
Qed.

(* Exercise 5.10 Using "pattern" and "rewrite". *)

Open Scope nat_scope.

Theorem nat_plus_permute :
  forall n m p : nat, n + m + p = n + p + m.
Proof.
  intros n m p.
  rewrite plus_assoc_reverse.
  rewrite plus_assoc_reverse.
  rewrite (plus_comm n (m + p)).
  rewrite (plus_comm n (p + m)).
  rewrite (plus_comm m p).
  trivial.
Qed.

(* Exercise 5.11 Transitivity of Leibniz equality. *)

Theorem eq_trans :
  forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros TA x y z h1 h2.
  rewrite h1; assumption.
Qed.

Theorem eq_trans' :
  forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros TA x y z h1.
  rewrite h1; trivial.
Qed.

Theorem eq_trans'' :
  forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros TA x y z h1.
  pattern y at 1.
  apply eq_ind with TA x;
    [ trivial
    | assumption
    ].
Qed.

(* Exercise 5.12 *)

(* Exercise 5.13 On Negation (impredicative definition). *)
(* Exercise 5.14 An impredicative definition of equality. *)
(* Exercise 5.15 Some impredicative definitions. *)
(* Exercise 5.16 An impredicative definition of "<=". *)

End Exercises.

End EverydayLogic.
