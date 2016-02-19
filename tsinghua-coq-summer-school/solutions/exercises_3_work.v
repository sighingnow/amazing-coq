(* Solution for exercieses in Tsinghua Coq Summber School.
  Exercise for leture 3: Proofs in Proposition Logic and Predicate Logic by Pierre Castéran. *)

(** This file contains some lemmas you will have to prove, i.e. replacing
   the "Admitted" joker with a sequence of tactic calls, terminated with a
   "Qed" command.

   Each lemma should be proved several times :
   first using only elementary tactics :
   intro[s], apply, assumption
   split, left, right, destruct.
   exists, rewrite
   assert (only if you don't find another solution)


   Then, use tactic composition, auto, tauto, firstorder.


Notice that, if you want to keep all solutions, you may use various
identifiers like in the given example : imp_dist, imp_dist' share
the same statement, with different interactive proofs.
*)

Section Minimal_propositioal_logic.

Variables P Q R S : Prop.

Lemma imp_dist : (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros H H0 p.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

Lemma imp_dist' : (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros H H0 p;apply H.
  assumption.
  apply H0;assumption.
Qed.

Lemma id_P : P -> P.
Proof.
  intro H.
  assumption.
Qed.

Lemma id_P' : P -> P.
Proof.
  intros h1.
  apply h1.
Qed.

Lemma id_PP : (P -> P) -> P -> P.
Proof.
  intros h1 h2.
  apply h2.
Qed.

Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros h1 h2 h3.
  apply h2; apply h1; apply h3.
Qed.

Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
Proof.
  intros h1 h2 h3.
  apply h1; [apply h3 | apply h2].
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros h1 h2 h3.
  apply h1; apply h2.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros h1 h2.
  apply h1; [apply h2 | apply h2].
Qed.

Lemma delta_impR : (P -> Q) -> P -> P -> Q.
Proof.
  intros h1 h2 h3.
  apply h1; apply h2.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
  intros h1 h2 h3 h4.
  apply h3.
  apply h1; apply h4.
  apply h2; apply h4.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
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

End Minimal_propositioal_logic.

(** Same exercise as the previous one, with full intuitionistic propositional
   logic

   You may use the tactics intro[s], apply, assumption, destruct,
                           left, right, split and try to use tactic composition *)

Section propositional_logic.

Variables P Q R S T : Prop.

Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intro h1.
  split; [split | idtac]; apply h1.
Qed.

Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
Proof.
  intros h1 h2.
  elim h1.
  intros h3 h4.
  split; [apply h3 | apply h4]; apply h2.
Qed.

Lemma not_contrad :  ~(P /\ ~P).
Proof.
  intros h1.
  elim h1.
  intros h2 h3.
  apply h3; apply h2.
Qed.

Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
Proof.
  intros h1.
  elim h1.
  intros h2 h3.
  elim h2;
    [ intros h4; elim h3; apply h4
    | trivial
    ].
Qed.

Lemma not_not_exm : ~ ~ (P \/ ~ P).
Proof.
  intros h1.
  elim h1; right; intro h2.
  elim h1; left; apply h2.
Qed.

Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros h1.
  split; intros h2; elim h1; [left | right]; assumption.
Qed.

Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros h1 h2.
  elim h2; (* "unfold not in h1;" *) apply h1.
Qed.

Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros h1 h2.
  elim h2.
  intros h3 h4.
  elim h1;
    [ intros h5; apply h5
    | intros h6; apply h6
    ];
    assumption.
Qed.

End propositional_logic.

Section First_Order_Logic.

Variable A : Set.
Variables
  (P Q : A -> Prop)
  (R : A -> A -> Prop).


Lemma forall_imp_dist : (
  forall x : A, P x -> Q x) -> (
    forall x : A, P x) ->
      forall x : A, Q x.
Proof.
  intros h1 h2 x.
  apply h1; apply h2.
Qed.

Lemma forall_perm : (
  forall x y : A, R x y) ->
    forall y x, R x y.
Proof.
  intros h1 y x.
  apply h1.
Qed.

Lemma forall_delta : (
  forall x y : A, R x y) ->
    forall x, R x x.
Proof.
  intros h1 x.
  apply h1.
Qed.

Lemma exists_or_dist : (
  exists x : A, P x \/ Q x) <-> (
    exists x, P x) \/ (
      exists x, Q x).
Proof.
  split.

  intros h1; elim h1.
  intros x h2; elim h2;
    intros;
      [ left
      | right
      ];
    exists x; assumption.

  intros h1; elim h1;
    intros h2; elim h2;
    intros x h3;
    exists x;
      [ left
      | right
      ];
    assumption.
Qed.

Lemma exists_imp_dist : (
  exists x : A, P x -> Q x) -> (
    forall x : A, P x) ->
      exists x:A, Q x.
Proof.
  intros h1 h2.
  elim h1.
  intros x h3.
  exists x.
  apply h3; apply h2.
Qed.

Lemma not_empty_forall_exists :
  forall a : A, (
    forall x : A, P x) ->
      exists x : A, P x.
Proof.
  intros a h1.
  exists a.
  apply h1.
Qed.

Lemma not_ex_forall_not : ~ (
  exists x : A, P x) <->
    forall x : A, ~ P x.
Proof.
  split.

  intros h1 x h2.
  elim h1.
  exists x.
  apply h2.

  intros h1 h2.
  elim h2.
  intros x.
  apply h1.
Qed.

Lemma singleton_forall_eq : (
  exists x : A,
    forall y : A, x = y) ->
      forall z t : A, z = t.
Proof.
  intros h1 z t.
  elim h1.
  intros x h2.
  rewrite <- (h2 t).
  apply eq_sym. (* rewrite goal using the symmetry of equal relation. *)
  rewrite <- (h2 z).
  reflexivity.
Qed.

Print singleton_forall_eq.

Section S1.

Variables  (f g : A -> A).

Hypothesis f_g_perm :
  forall x : A, f (g x) = g (f x).
Hypothesis g_idempotent :
  forall x : A, g (g x) = g x.
Hypothesis f_idempotent :
  forall x : A, f (f x) = f x.

Lemma L :
  forall z, g (f (g (f (g (f z))))) = f (g z).
Proof.
  intros z.
  rewrite f_g_perm.
  rewrite g_idempotent.
  rewrite f_idempotent.
  rewrite f_g_perm.
  rewrite g_idempotent.
  rewrite f_idempotent.
  rewrite f_g_perm.
  trivial.
Qed.

Lemma L':  (
  forall x : A, ~ x = f x) -> ~ (
    exists y : A, True).
Proof.
  intros h1 h2.
  (* introduce a variable "x" into hypotheses. *)
  elim h2.
  intros x h3.
  apply (h1 (f x)).
  rewrite f_idempotent.
  trivial.
Qed.

End S1.
