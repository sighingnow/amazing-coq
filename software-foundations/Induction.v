(* Code for Software Foundations, Chapter 3: Induction: Proof by Induction *)

Require Import Arith.
Require Import Basics.

(* basic_induction *)

Theorem mult_0_r :
  forall n : nat, n * O = O.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. apply IHn.
Qed.

Theorem plus_n_Sm :
  forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_comm :
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  + induction m.
    - simpl. reflexivity.
    - simpl. rewrite <- IHm. simpl. reflexivity.
  + rewrite <- plus_n_Sm.
    rewrite <- IHn.
    simpl. reflexivity.
Qed.

Theorem plus_assoc :
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

(* double_plus *)

Fixpoint double (n : nat) {struct n} : nat :=
  match n with
    | O    => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus :
  forall n : nat, double n = n + n.
Proof.
  induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn.
    apply eq_S.
    apply plus_n_Sm.
Qed.

(* evenb_S *)

Fixpoint evenb (n : nat) {struct n} : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Theorem evenb_S :
  forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  induction n.
  + simpl; reflexivity.
  + rewrite IHn.
    simpl.
    assert(h1 : forall x, negb (negb x) = x).
    - induction x; simpl; reflexivity.
    - rewrite h1; reflexivity.
Qed.

(* destruct_induction *)

(* The difference between "destruct" and "induction":
  + the tactic "destruct" is just a case analyser, enumerate all constructors
    of the argument type, the proove one by one.
  + the tactic "induction" is applied on a induction data type, then proove the
    base case is correct, and introduce a hypothesis into environment (context),
    then proove the successor case in current context, according to the
    principle of induction, the universal quantification is qed. *)

(* mult_comm *)

Theorem plus_swap :
  forall n m p, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  rewrite plus_assoc.
  rewrite (plus_comm n m).
  reflexivity.
Qed.

Theorem mult_comm :
  forall m n, m * n = n * m.
Proof.
  intros m n.
  induction n.
  + simpl.
    induction m.
    - reflexivity.
    - simpl; assumption.
  + simpl mult.
    rewrite <- IHn.
    pattern m at 2.
    assert (mult_x_1 : forall x, x = x * 1).
    * induction x.
      - simpl; trivial.
      - simpl; rewrite <- IHx; reflexivity.
    * rewrite mult_x_1 with (x := m).
      rewrite <- mult_plus_distr_l.
      simpl; reflexivity.
Qed.

(* more exercises *)

Theorem leb_refl :
  forall n, true = leb n n.
Proof.
  induction n.
  + simpl; trivial.
  + simpl; assumption.
Qed.

Theorem zero_nbeq_S :
  forall n, beq_nat O (S n) = false.
Proof.
  induction n.
  + simpl; trivial.
  + simpl; trivial.
Qed.

Theorem andb_false_r :
  forall b, andb b false = false.
Proof.
  destruct b; simpl; reflexivity.
Qed.

Theorem plus_ble_compat_l :
  forall n m p, leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  induction p.
  + simpl; trivial.
  + simpl; assumption.
Qed.

Theorem S_nbeq_0 :
  forall n, beq_nat (S n) O = false.
Proof.
  trivial.
Qed.

Theorem mult_1_l :
  forall n, 1 * n = n.
Proof.
  destruct n.
  + simpl; reflexivity.
  + simpl.
    assert (h1 : forall m, m + 0 = m).
    * induction m.
      - simpl; reflexivity.
      - simpl; rewrite IHm; reflexivity.
    * rewrite h1 with (m := n).
      reflexivity.
Qed.

Theorem all3_spec :
  forall b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  destruct b, c; simpl; trivial.
Qed.

Theorem mult_plus_distr_r :
  forall n m p : nat, (n + m) * p = (n * p) + (m * p).
Proof.
  induction n, m; intros p.
  - simpl; reflexivity.
  - simpl; reflexivity.
  - simpl.
    rewrite IHn with (m := 0) (p := p).
    rewrite plus_assoc.
    trivial.
  - simpl.
    rewrite IHn.
    simpl.
    repeat rewrite plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc :
  forall n m p, n * (m * p) = (n * m) * p.
Proof.
  induction n.
  - simpl; trivial.
  - simpl.
    intros m p.
    rewrite IHn with (m := m) (p := p).
    rewrite mult_plus_distr_r.
    reflexivity.
Qed.

(* beq_nat_refl *)

Theorem beq_nat_refl :
  forall n : nat, true = beq_nat n n.
Proof.
  induction n.
  - trivial.
  - simpl; assumption.
Qed.

(* plus_swap' *)

Theorem plus_swap' :
  forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  repeat rewrite plus_assoc.
  replace (m + n) with (n + m).
  - reflexivity.
  - rewrite plus_comm.
    reflexivity.
Qed.

(* binary_commute *)

Theorem bin_to_nat_pres_incr :
  forall x : bin, bin_to_nat (incr x) = S (bin_to_nat x).
Proof.
  induction x.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl.
    rewrite IHx.
    simpl.
    rewrite Nat.add_succ_r.
    reflexivity.
Qed.

(* binary_inverse *)

Fixpoint nat_to_bin (n : nat) {struct n} : bin :=
  match n with
    | O => zero
    | S n' => incr (nat_to_bin n')
  end.

Theorem double_convert :
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n.
  + simpl; trivial.
  + simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite IHn.
    reflexivity.
Qed.

Theorem double_convert_reverse :
  forall b : bin, nat_to_bin (bin_to_nat b) = b.
Proof.
  induction b.
Abort.
(* The problem is that "twice zero = zero" ! It destory the induction principle. *)

Definition normalize (b : bin) : bin :=
  nat_to_bin (bin_to_nat b).

Theorem normalize_identical :
  forall b : bin, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  unfold normalize.
  reflexivity.
Qed.

(* plus_comm_informal *)

(* Theorem: Addition is commutative.
  Proof: by induction on n,
    base case: n = 0
      0 + m = m, m + 0 = m, reflexivity.
      then, forall k, k + m = m + k holds.
    inductive step: n = 1 + k
      1 + k + m = 1 + m + k = m + 1 + k.
    Qed. *)

(* beq_nat_refl_informal *)

(* Theorem: true = beq_nat n n for any n.
  Proof: by induction on n,
    base case: n = 0
      true = beq_nat 0 = 0 is trivial.
      then, forall k,  true beq_nat k = k holds.
    inductive step: n = S k
      beq_nat (S k) (S k)
      = beq_nat k k (* unfold the beq_nat. *)
      = true.
    Qed. *)
