(* Code for Software Foundations, Chapter 7: Logic: Logic in Coq *)

Require Import Arith.
Require Import Arith.Even.
Require Import List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Poly.
Require Import Tactics.

(* and_exercise *)

Example and_exercise :
  forall n m : nat, n + m = O -> n = O /\ m = O.
Proof.
  induction n, m.
  + simpl; intros; split; assumption.
  + simpl; intros; split; [reflexivity | assumption].
  + simpl; inversion 1.
  + simpl; inversion 1.
Qed.

(* and_assoc *)

Theorem and_assoc :
  forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [p [q r]].
  repeat split; assumption.
Qed.

(* mult_eq_O *)

Theorem mult_eq_O :
  forall n m, n * m = O -> n = 0 \/ m = 0.
Proof.
  induction n, m.
  + simpl; left; reflexivity.
  + simpl; left; reflexivity.
  + simpl; right; reflexivity.
  + simpl; inversion 1.
Qed.

(* or_commut *)

Theorem or_commut :
  forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q [p | q].
  + right; assumption.
  + left; assumption.
Qed.

(* ex_falso_quodlibet *)

Theorem ex_falso_quodlibet :
  forall P : Prop, False -> P.
Proof.
  intros P false.
  apply False_ind; assumption. (* or: "elim false." *)
Qed.

(* not_implies_our_not *)

Fact not_implies_our_not :
  forall P, ~ P -> (forall Q, P -> Q).
Proof.
  intros P negp Q p.
  elim negp; apply p.
Qed.

(* zero_not_one *)

Theorem zero_not_one :
  ~ (0 = 1).
Proof.
  intros contradiction.
  inversion contradiction.
Qed.

(* double_neg_inf *)

Theorem double_neg_inf :
  forall P : Prop, P -> ~ ~ P.
Proof.
  intros P p negp.
  elim negp; apply p.
Qed.

(* contrapositive *)

Theorem contrapositive :
  forall P Q : Prop, (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q h1 h2 h3.
  elim h2.
  apply h1; apply h3.
Qed.

(* not_both_true_and_false *)

Theorem not_both_true_and_false :
  forall P : Prop, ~ (P /\ ~ P).
Proof.
  intros P contradiction.
  inversion contradiction as [p negp].
  elim negp; apply p.
Qed.

(* iff_properties *)

Theorem iff_refl :
  forall P : Prop, P <-> P.
Proof.
  reflexivity.
Qed.

Theorem iff_trans :
  forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R h1 h2.
  split.
  + intros p.
    apply h2; apply h1; assumption.
  + intros r.
    apply h1; apply h2; assumption.
Qed.

(* or_distributes_over_and *)

Theorem or_distributes_over_and :
  forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  + intros [p | [q r]].
    * split; left; assumption.
    * split; right; assumption.
  + intros [[p1 | q] [p2 | r]]. (* Important !! *)
    * left; assumption.
    * left; assumption.
    * left; assumption.
    * right; split; assumption.
Qed.

(* dist_not_exists *)

Theorem dist_not_exists :
  forall (X : Type) (P : X -> Prop), (
    forall x, P x) -> ~ (
      exists x, ~ P x).
Proof.
  intros X P h1 h2.
  elim h2.
  intros x h3.
  elim h3.
  apply h1.
Qed.

(* dist_exists_or *)

Theorem dist_exists_or :
  forall (X : Type) (P Q : X -> Prop), (
    exists x, P x \/ Q x) <-> (
      exists x, P x) \/ (
        exists x, Q x).
Proof.
  intros X P Q.
  split.
  + intros h1.
    elim h1.
    intros x [hp | hq].
    - left; exists x; assumption.
    - right; exists x; assumption.
  + intros [hp | hq].
    - elim hp.
      intros x p.
      exists x; left; assumption.
    - elim hq.
      intros x p.
      exists x; right; assumption.
Qed.

(* in_application *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
    | nil   => False
    | t::ts => x = t \/ In x ts
  end.

(* in_map_iff *)

Lemma in_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  induction l.
  + simpl; trivial.
  + simpl.
    intros x [hx_eq_a | hx_in_l].
    - left; rewrite hx_eq_a; reflexivity.
    - right; apply IHl; assumption.
Qed.

Lemma in_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
      exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  + intros h1.
    induction l as [|x l].
    - simpl in h1.
      elim h1.
    - induction h1 as [|h1].
      * exists x.
        split;
          [ rewrite H
          | simpl; left
          ]; reflexivity.
      * apply IHl in h1.
        destruct h1 as [x' h1].
        exists x'.
        split;
          [ apply h1
          | simpl; right; apply h1
          ].
  + intros [x [h1 h2]].
    simpl.
    induction l as [|a l].
    - simpl.
      inversion h2.
    - simpl in h2.
      destruct h2 as [h2l | h2r].
      * simpl.
        rewrite h2l in h1.
        rewrite h1.
        left; reflexivity.
      * simpl.
        right; apply IHl; apply h2r.
Qed.

(* in_app_iff *)

Lemma logic_or_comm :
  forall A B C D : Prop, A \/ B \/ C \/ D -> (A \/ B) \/ C \/ D.
Proof.
  intros A B C D [a | [b | [c | d]]].
  + left; left; assumption.
  + left; right; assumption.
  + right; left; assumption.
  + right; right; assumption.
Qed.

Lemma in_app_iff :
  forall A l l' (a : A), In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  split; induction l, l'.
  + simpl. inversion 1.
  + simpl.
    intros h1.
    right; assumption.
  + simpl.
    intros [h1 | h2].
    * left; left; assumption.
    * apply IHl in h2.
      destruct h2 as [h3 | h4].
      - left; right; assumption.
      - inversion h4.
  + simpl.
    simpl in IHl.
    intros [h1 | h2].
    * left; left; assumption.
    * apply IHl in h2.
      destruct h2 as [h3 | [h4 | h5]].
      - left; right; assumption.
      - right; left; assumption.
      - right; right; assumption.
  + intros [h1 | h2].
    * inversion h1.
    * inversion h2.
  + simpl.
    intros [h1 | [h2 | h3]].
    * inversion h1.
    * left; assumption.
    * right; assumption.
  + simpl.
    intros [[h1 | h2] | h3].
    * left; assumption.
    * right; rewrite app_nil_r; assumption.
    * inversion h3.
  + simpl.
    intros [[h1 | h2] | [h3 | h4]].
    * left; assumption.
    * right.
      apply IHl.
      left; assumption.
    * right.
      apply IHl.
      simpl.
      right; left; assumption.
    * right.
      apply IHl.
      simpl.
      right; right; assumption.
Qed.

(* all *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
    | nil   => True
    | x::xs => P x /\ All P xs
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T), (
    forall x, In x l -> P x) <-> All P l.
Proof.
  split; induction l as [|a l].
  + intros h1.
    simpl; trivial.
  + simpl.
    intros h1.
    split.
    - apply h1.
      left; reflexivity.
    - apply IHl.
      intros x h2.
      apply h1.
      right; assumption.
  + intros h1 x h2.
    inversion h2.
  + simpl.
    intros [h1 h2] x [h3 | h4].
    - rewrite h3; assumption.
    - apply IHl; assumption.
Qed.

(* combine_odd_even *)

Definition combine_odd_even (P Q : nat -> Prop) : nat -> Prop :=
  fun (x : nat) => match Nat.even x with
    | true  => P x
    | false => Q x
  end.

Theorem combine_odd_even_intro :
  forall (P Q : nat -> Prop) (n : nat),
    (Nat.even n = true -> P n)
      -> (Nat.even n = false -> Q n)
        -> combine_odd_even P Q n.
Proof.
  intros P Q n h1 h2.
  unfold combine_odd_even.
  destruct (Nat.even n).
  + apply h1; reflexivity.
  + apply h2; reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (P Q : nat -> Prop) (n : nat),
    combine_odd_even P Q n -> Nat.even n = true -> P n.
Proof.
  intros P Q n h1 h2.
  unfold combine_odd_even in h1.
  destruct (Nat.even n).
  + assumption.
  + inversion h2.
Qed.

Theorem combine_odd_even_elim_even :
  forall (P Q : nat -> Prop) (n : nat),
    combine_odd_even P Q n -> Nat.even n = false -> Q n.
Proof.
  intros P Q n h1 h2.
  unfold combine_odd_even in h1.
  destruct (Nat.even n).
  + inversion h2.
  + assumption.
Qed.

(* tr_rev *)

Fixpoint tr_rev_aux {X} (l1 l2 : list X) : list X :=
  match l1 with
    | nil    => l2
    | x::l1' => tr_rev_aux l1' (x::l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  tr_rev_aux l nil.

Lemma tr_rev_aux_correct :
  forall (X : Type) (l1 l2 : list X), tr_rev_aux l1 l2 = tr_rev_aux l1 nil ++ l2.
Proof.
  induction l1 as [|a l1].
  + simpl; reflexivity.
  + intros l2.
    simpl.
    rewrite (IHl1 (a::nil)).
    rewrite (IHl1 (a::l2)).
    rewrite <- app_assoc.
    simpl; reflexivity.
Qed.

Theorem tr_rev_correct :
  forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  unfold tr_rev.
  induction x as [|x l].
  + simpl; reflexivity.
  + simpl.
    rewrite <- IHl.
    apply tr_rev_aux_correct.
Qed.

(* evenb_double *)

Lemma succ_transfer :
  forall n : nat, n + S (S n) = S n + S n.
Proof.
  induction n as [|n].
  + reflexivity.
  + simpl.
    rewrite Nat.add_succ_r.
    reflexivity.
Qed.

Theorem evenb_double :
  forall k, Nat.even (Nat.double k) = true.
Proof.
  induction k as [|k].
  + reflexivity.
  + simpl.
    destruct k as [|k'] eqn:k_ind.
    - simpl; reflexivity.
    - simpl.
      rewrite succ_transfer.
      apply IHk.
Qed.

(* evenb_double_conv *)

Theorem evenb_double_conv :
  forall n,
    exists k, n = if Nat.even n
      then Nat.double k
      else S (Nat.double k).
Proof.
  induction n as [|n].
  + exists O; reflexivity.
  + rewrite Nat.even_succ. (* The KEY step. *)
    destruct IHn as [x IHx].
    destruct (Nat.even n) eqn:x_odd_even.
    - exists x.
      rewrite <- IHx.
      assert (n_odd_even : Nat.even n = true -> Nat.odd n = false).
      * unfold Nat.odd; intros h1; rewrite h1; reflexivity.
      * rewrite n_odd_even;
          [ reflexivity
          | assumption
          ].
    - exists (S x).
      assert (n_odd_even : Nat.even n = false -> Nat.odd n = true).
      * unfold Nat.odd; intros h1; rewrite h1; reflexivity.
      * { rewrite n_odd_even.
          + rewrite IHx; unfold Nat.double.
            simpl.
            apply eq_S; rewrite Nat.add_succ_r; reflexivity.
          + assumption.
        }
Qed.

(* even_bool_prop *)

Theorem even_bool_prop :
  forall n, Nat.even n = true <->
    exists k, n = Nat.double k.
Proof.
  intros n.
  split.
  + intros h1.
    destruct (evenb_double_conv n) as [k Hk]. (* The KEY step. *)
    rewrite Hk.
    exists k.
    rewrite h1; reflexivity.
  + intros [k Hk].
    rewrite Hk.
    apply evenb_double.
Qed.

(* beq_nat_true_iff *)

Theorem beq_nat_true_iff :
  forall n1 n2, beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  split.
  + apply beq_nat_true.
  + intros h1.
    rewrite h1.
    rewrite <- beq_nat_refl; reflexivity.
Qed.

(* logical_connectives *)

Theorem andb_true_iff :
  forall b1 b2 : bool, andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  split.
  + induction b1, b2.
    - simpl; split; reflexivity.
    - simpl; split; [reflexivity | assumption].
    - simpl; split; [assumption | reflexivity].
    - simpl; split; assumption.
  + intros [h1 h2].
    rewrite h1; rewrite h2; simpl; reflexivity.
Qed.

Theorem orb_true_iff :
  forall b1 b2 : bool, orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  split.
  + induction b1, b2.
    - simpl; left; reflexivity.
    - simpl; left; reflexivity.
    - simpl; right; reflexivity.
    - inversion 1.
  + intros [h1 | h2].
    - rewrite h1; reflexivity.
    - rewrite h2.
      destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

(* beq_nat_false_iff *)

Theorem beq_nat_false_iff :
  forall x y : nat, beq_nat x y = false <-> x <> y.
Proof.
  intros x y.
  split.
  + intros h1 h2.
    rewrite h2 in h1.
    rewrite <- beq_nat_refl in h1.
    inversion h1.
  + intros h1.
    destruct (beq_nat x y) eqn:x_eq_y.
    - apply beq_nat_true in x_eq_y.
      elim h1; assumption.
    - reflexivity.
Qed.

(* beq_list *)

Fixpoint beq_list {A : Type} (beq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
    | nil, nil       => true
    | x::l1', y::l2' => beq x y && beq_list beq l1' l2'
    | _, _           => false
  end.

Theorem beq_list_true_iff :
  forall (A : Type) (beq : A -> A -> bool), (
    forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
      forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq h1.
  induction l1 as [|a l1].
  + induction l2 as [|b l2].
    - split; reflexivity.
    - split; intros h2; inversion h2.
  + induction l2 as [|b l2].
    - split; inversion 1.
    - simpl; split.
      * intros h2.
        apply andb_true_iff in h2.
        destruct h2 as [h2 h3].
        apply h1 in h2.
        apply IHl1 in h3.
        rewrite h2; rewrite h3; reflexivity.
      * intros h2.
        apply andb_true_iff.
        injection h2 as h2 h3.
        rewrite h2; rewrite <- h3.
        split; [apply h1 | apply IHl1]; reflexivity.
Qed.

(* All_forallb *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | nil   => true
    | x::l' => test x && forallb test l'
  end.

Theorem forallb_true_iff :
  forall X test (l : list X), forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  induction l.
  + simpl; split; [ trivial | reflexivity ].
  + simpl; split.
    * intros h1; apply andb_true_iff in h1; destruct h1 as [h1 h2]; split.
      - assumption.
      - apply IHl; assumption.
    * intros [h1 h2].
      apply andb_true_iff.
      split.
      - assumption.
      - apply IHl in h2; assumption.
Qed.

(* restricted_excluded_middle *)

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Theorem restricted_excluded_middle :
  forall P b, (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P b h1.
  destruct b eqn:b_value.
  - left; apply h1; reflexivity.
  - right; rewrite h1; inversion 1.
Qed.

(* excluded_middle_irrefutable *)

Theorem excluded_middle_irrefutable :
  forall P : Prop, ~ ~ (P \/ ~ P).
Proof.
  unfold not; intros P h1.
  apply h1.
  right. intros p. apply h1.
  left; apply p.
Qed.

(* not_exist_dist *)

Theorem not_exist_dist :
  excluded_middle ->
    forall (X : Type) (P : X -> Prop), ~ (
      exists x, ~ P x) -> (
        forall x, P x).
Proof.
  unfold excluded_middle.
  intros em X P h1 x.
  destruct (em (P x)) as [p | negp].
  + assumption.
  + elim h1.
    exists x; assumption.
Qed.

