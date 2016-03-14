(* Code for Coq'Art, Chapter 3: Propositions and Proofs. *)

Section PropositionsAndProofs.

Variable P Q R S T : Prop.

(* Examples *)
Section Examples.

Section MinimalPropositionalLogic.

Theorem imp_trans_theorem : (P -> Q) -> (Q -> R) -> P -> R.
(* Detailed proof *)
Proof.
  intros h1 h2 h3.
  apply h2.
  apply h1.
  apply h3. (* assumption. *)
Qed.
Print imp_trans_theorem.

Theorem imp_trans' : (P -> Q) -> (Q -> R) -> P -> R.
(* Auto Proof. *)
Proof.
  auto.
Qed.
Print imp_trans'.

Hypothesis hypo1 : P -> Q -> R.

Lemma l1 : P -> Q -> R.
Proof.
  apply hypo1.
Qed.
Print l1.

Theorem delta : (P -> P -> Q) -> P -> Q.
Proof.
  (* detailed proof:
    intros h1 h2.
    apply h1.
    apply h2.
    apply h2. *)
  exact (fun (h1 : P -> P -> Q)(h2 : P) => h1 h2 h2).
Qed.
Print delta.

(* Theorem delta : (P -> P -> Q) -> P -> Q.
Proof (fun (h1 : P -> P -> Q)(h2 : P) => h1 h2 h2).
Print delta. *)

Theorem apply_example : (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
Proof.
  intros h1 h2 h3.
  apply h1.
  apply h2.
  apply h3.
Qed.
Print apply_example.

Theorem imp_dist : (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros h1 h2 h3.
  apply h1.
  apply h3.
  apply h2.
  apply h3.
Qed.
Print imp_dist.

Theorem k : P -> Q -> P.
Proof.
  intros h1 h2.
  apply h1.
Qed.
Print k.

Section ProofOfTripleImpl.

Hypothesis hypo2 : P.
Hypothesis hypo3 : ((P -> Q) -> Q) -> Q.

Lemma l2 : (P -> Q) -> Q.
Proof (fun (h1 : P -> Q) => h1 hypo2).

Theorem triple_impl : Q.
Proof (hypo3 l2).

End ProofOfTripleImpl.

Print triple_impl.
Print l2.

Theorem then_example : P -> Q -> (P -> Q -> R) -> R.
Proof.
  intros h1 h2 h3.
  apply h3; assumption.
Qed.

Theorem triple_impl_one_shot : (((P -> Q) -> Q) -> Q) -> P -> Q.
Proof.
  intros h1 h2.
  apply h1; intro h3; apply h3; apply h2.
Qed.

Theorem compose_example : (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  intros h1 h2 h3.
  apply h1; [assumption | apply h2; assumption].
Qed.

Theorem orelse_example : (P -> Q) -> R -> ((P -> Q) -> R -> (T -> Q) -> T) -> T.
Proof.
  intros h1 h2 h3.
  apply h3; (assumption || intros h4).
Abort. (* can't be proved. *)

Lemma idtac_example : (P -> Q) -> (P -> R) -> (P -> Q -> R -> T) -> P -> T.
Proof.
  intros h1 h2 h3 h4.
  apply h3; [idtac | apply h1 | apply h2]; assumption.
Qed.

Lemma then_fail_example : (P -> Q) -> (P -> Q).
Proof.
  intros h1; apply h1; fail.
Qed.

Lemma try_example : (P -> Q -> R -> T) -> (P -> Q) -> (P -> R -> T).
Proof.
  intros h1 h2 h3 h4.
  apply h1; try assumption.
  apply h2; assumption.
Qed.

Section CutTacticExample.

(* cut tactic: for goal Q, impose these two subgoals:
  + P
  + P -> Q
  base on MP(Modus Ponens) rules, the goal can be proved by these two subgoals. *)

Hypothesis
  (h1 : P -> Q)
  (h2 : Q -> R)
  (h3 : (P -> R) -> T -> Q)
  (h4 : (P -> R) -> T).

Theorem cut_example : Q.
Proof.
  cut (P -> R).
  intros h5.
  apply h3;
    [ apply h5
    | apply h4; apply h5
    ].
  intros h6; apply h2; apply h1; apply h6.
Qed.
Print cut_example.

End CutTacticExample.

End MinimalPropositionalLogic.

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 3.1 *)
Check ((P -> Q) -> (Q -> R) -> P -> R).

(* Exercise 3.2 and 3.3 *)
Lemma id_P : P -> P.
Proof.
  intros h1.
  apply h1.
Qed.
Print id_P.

Lemma id_PP : (P -> P) -> (P -> P).
Proof.
  intro h1.
  apply h1.
Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros h1 h2 h3.
  apply h2.
  apply h1.
  apply h3.
Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros h1.
  intros h2 h3.
  apply h1.
  apply h3.
  apply h2.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros h1 h2 h3.
  apply h1.
  apply h2.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros h1 h2.
  apply h1.
  apply h2.
  apply h2.
Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof.
  intros h1 h2.
  apply h1.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros h1 h2 h3 h4.
  apply h3.
  apply h1.
  apply h4.
  apply h2.
  apply h4.
Qed.
Print diamond.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
(* Perice formula: ((P -> Q) -> P) -> P. can't be proved by Coq (Calculus of
  Constructions), it uses normalization properties in typed lambda-calculi. *)
Proof.
  intros h1.
  apply h1.
  intros h2.
  apply h2.
  intros h3.
  apply h1.
  intros h4.
  apply h3.
Qed.
Print weak_peirce.

(* Exercise 3.4 *)

(** Typing rules used in minimum propositional logic is: Prod, Lam, App* and Var.
  for a formula q:
  + if q is a variable, it can be solved by assumption tactic.
  + if q is an abstraction, it can be simplified by intro tactic.
  + if q is an application, it can be solved by apply tactic. **)

(* Exercise 3.5 *)

Section Example_3_5.

Hypothesis
  (h1 : P -> Q)
  (h2 : Q -> R)
  (h3 : (P -> R) -> T -> Q)
  (h4 : (P -> R) -> T).

Lemma cut_example' : Q.
Proof.
  apply h3.
  intros h5.
  apply h2; apply h1; apply h5.
  apply h4.
  intros h6.
  apply h2; apply h1; apply h6.
Qed.
End Example_3_5.
Print cut_example.
Print cut_example'.

(* Exercise 3.6 *)

Section AutoExample.

(** Pattern: according to law of transfer, it's easy to construct a theorem/lemma
  need to be proved at least arbitrary n steps. **)

Variables P0 P1 P2 P3 P4 P5 : Prop.
Lemma auto_example :
  (P0 -> P1) ->
  (P1 -> P2) ->
  (P2 -> P3) ->
  (P3 -> P4) ->
  (P4 -> P5) ->
  P0 -> P5.
Proof.
  auto 6.
Qed.
Print auto_example.

End AutoExample.

End Exercises.

End PropositionsAndProofs.

(* Abstraction (with universal quatification). *)
Print imp_dist.

