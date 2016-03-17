(* Code for Software Foundations, Chapter 4: Lists: Working with Structured Data *)

Require Import Arith.

(* snd_fst_is_swap *)

Module Natprod.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
    | pair a _ => a
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | pair _ b => b
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (a, b) => (b, a)
  end.

Theorem snd_fst_is_swap :
  forall p : natprod, (snd p, fst p) = swap_pair p.
Proof.
  induction p.
  simpl; reflexivity.
Qed.

(* fst_swap_is_snd *)

Theorem fst_swap_is_snd :
  forall p : natprod, fst (swap_pair p) = snd p.
Proof.
  induction p.
  simpl; reflexivity.
Qed.

End Natprod.

Module Natlist.

(* list_funs *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation " [ ] " := nil.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) .. ).

Fixpoint nonzeros (l : natlist) {struct l} : natlist :=
  match l with
    | nil       => nil
    | cons x xs => match x with
      | O    => nonzeros xs
      | S _ => cons x (nonzeros xs)
    end
  end.

Fixpoint oddmembers (l : natlist) {struct l} : natlist :=
  match l with
    | nil       => nil
    | cons x xs => match Nat.odd x with
      | true  => cons x (oddmembers xs)
      | false => nil
    end
  end.

Fixpoint countoddmembers (l : natlist) {struct l} : nat :=
  match l with
    | nil       => O
    | cons x xs => match Nat.odd x with
      | true  => S (countoddmembers xs)
      | false => countoddmembers xs
    end
  end.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, xs              => xs
    | xs, nil              => xs
    | cons x xs, cons y ys => cons x (cons y (alternate xs ys))
  end.

(* bag_functions *)

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) {struct s} : nat :=
  match s with
    | nil       => O
    | cons x xs => match beq_nat v x with
      | true  => S (count v xs)
      | false => count v xs
    end
  end.

Definition sum : bag -> bag -> bag :=
  alternate.

Definition add (v : nat) (s : bag) : bag :=
  alternate (cons v nil) s.

Definition member (v : nat) (s : bag) : bool :=
  negb (beq_nat 0 (count v s)).

(* bag_more_functions *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | cons x xs => match beq_nat v x with
      | true => xs (* only remove the first appear of v. *)
      | false => cons x (remove_one v xs)
    end
  end.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | cons x xs => match beq_nat v x with
      | true => remove_all v xs (* remove all appears of v. *)
      | false => cons x (remove_all v xs)
    end
  end.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
    | nil => true
    | cons x xs => match member x s2 with
      | true => subset xs (remove_one x s2)
      | false => false
    end
  end.

(* bag_theorem *)

Locate "=?".

Lemma equal_refl :
  forall n : nat, n =? n = true.
Proof.
  induction n.
  + simpl; reflexivity.
  + simpl; assumption.
Qed.

Theorem bag_theorem :
  forall (n : nat) (s : bag), count n (add n s) = count n s + 1.
Proof.
  induction s.
  - simpl.
    rewrite equal_refl; trivial.
  - simpl.
    rewrite equal_refl.
    destruct (n =? n0).
    + simpl.
      apply eq_S.
      rewrite (Nat.add_1_r (count n s)).
      reflexivity.
    + rewrite (Nat.add_1_r (count n s)).
      reflexivity.
Qed.

(* list_exercises *)

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil       => O
    | cons x xs => S (length xs)
  end.

Fixpoint app (l1 l2 : natlist) {struct l1} : natlist :=
  match l1 with
    | nil       => l2
    | cons x xs => cons x (app xs l2)
  end.

Notation " x ++ y " := (app x y) (right associativity, at level 60).

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil       => nil
    | cons x xs => rev xs ++ [x]
  end.

Theorem app_nil_r :
  forall l : natlist, l ++ [] = l.
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl; rewrite IHl; reflexivity.
Qed.

Theorem app_nil_l :
  forall l,  [] ++ l = l.
Proof.
  reflexivity.
Qed.

Lemma append_assoc :
  forall l1 l2 l3, l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3.
Proof.
  reflexivity. (* "++" is right associativity *)
Qed.

Lemma cons_injection :
  forall n l1 l2, l1 = l2 -> cons n l1 = cons n l2.
Proof.
  intros n l1 l2 h1.
  induction l1, l2.
  + reflexivity.
  + elim h1; reflexivity.
  + elim h1; reflexivity.
  + rewrite h1; reflexivity.
Qed.

Lemma append_xs_l :
  forall l l1 l2, l1 = l2 -> l ++ l1 = l ++ l2.
Proof.
  induction l.
  + simpl; intros; assumption.
  + simpl.
    intros l1 l2 h1.
    rewrite (IHl l1 l2).
    - reflexivity.
    - assumption.
Qed.

Lemma append_xs_r :
  forall l l1 l2, l1 = l2 -> l1 ++ l = l2 ++ l.
Proof.
  intros l l1 l2 h1.
  induction l1, l2.
  + simpl. reflexivity.
  + rewrite h1; reflexivity.
  + rewrite h1; reflexivity.
  + rewrite h1; reflexivity.
Qed.

Lemma append_assoc_reverse :
  forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
  induction l1, l2.
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl; rewrite app_nil_r; reflexivity.
  + simpl; intros l3.
    apply (cons_injection n ((l1 ++ cons n0 l2) ++ l3) (l1 ++ cons n0 (l2 ++ l3))).
    rewrite IHl1.
    trivial. (* detailed proof:
      "apply append_xs_l.
       simpl; reflexivity." *)
Qed.

Lemma rev_append_rev :
  forall l1 l2, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1.
  + simpl.
    intros l2.
    induction (rev l2).
    - simpl; reflexivity.
    - simpl; rewrite <- IHn; reflexivity.
  + simpl; intros l2. rewrite IHl1.
    rewrite append_assoc_reverse; reflexivity.
Qed.

Theorem rev_involutive :
  forall l : natlist, rev (rev l) = l.
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl.
    rewrite rev_append_rev.
    rewrite IHl.
    simpl; reflexivity.
Qed.

Theorem app_assoc4 :
  forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  assert(h1 : ((l1 ++ l2) ++ l3) ++ l4 = (l1 ++ l2) ++ l3 ++ l4).
  + apply append_assoc_reverse.
  + rewrite h1.
    rewrite <- (append_assoc_reverse l1 l2 (l3 ++ l4)).
    reflexivity.
Qed.

Theorem noezeros_app :
  forall l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  induction l1.
  + simpl; reflexivity.
  + induction n.
    - simpl; assumption.
    - simpl.
      intros l2.
      apply cons_injection.
      apply (IHl1 l2).
Qed.

(* beq_natlist *)

Fixpoint beq_natlist (l1 l2 : natlist) {struct l1} : bool :=
  match l1, l2 with
    | nil, nil             => true
    | cons x xs, cons y ys => andb (beq_nat x y) (beq_natlist xs ys)
    | _, _                 => false
  end.

Theorem beq_natlist_refl :
  forall l, true = beq_natlist l l.
Proof.
  induction l.
  - simpl; reflexivity.
  - simpl.
    assert (l1 : true = (n =? n)).
    + induction n.
      * simpl; reflexivity.
      * trivial.
    + rewrite <- l1.
      rewrite <- IHl.
      simpl; reflexivity.
Qed.

(* bag_proofs *)

Theorem count_member_nonzero :
  forall s : bag, leb 1 (count 1 (cons 1 s)) = true.
Proof.
  induction s.
  + simpl; reflexivity.
  + simpl; reflexivity.
Qed.

Theorem ble_n_Sn :
  forall n, leb n (S n) = true.
Proof.
  induction n.
  + trivial.
  + rewrite <- IHn.
    simpl.
    reflexivity.
Qed.

Theorem remove_decrease_count :
  forall s : bag, leb (count O (remove_one O s)) (count O s) = true.
Proof.
  induction s.
  + simpl; reflexivity.
  + induction n.
    - simpl; apply ble_n_Sn.
    - simpl; apply IHs.
Qed.

(* bag_count_sum *)

Theorem bag_count_sum :
  forall n s1 s2, count n s1 + count n s2 = count n (sum s1 s2).
Proof.
  induction s1, s2.
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl.
    induction (Nat.eqb n n0).
    rewrite <- plus_n_O; reflexivity.
    rewrite <- plus_n_O; reflexivity.
  + simpl.
    induction (Nat.eqb n n0).
    - simpl.
      apply eq_S.
      induction (Nat.eqb n n1).
      * rewrite Nat.add_succ_r.
        apply eq_S.
        apply (IHs1 s2).
      * apply (IHs1 s2).
    - induction (Nat.eqb n n1).
      * rewrite Nat.add_succ_r.
        apply eq_S.
        apply (IHs1 s2).
      * apply (IHs1 s2).
Qed.

(* rev_injective *)

Theorem rev_injective :
  forall l1 l2 : natlist, rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 h1.
  (* use "rev_involutive : rev (rev l) = l". *)
  rewrite <- (rev_involutive l1).
  rewrite <- (rev_involutive l2).
  rewrite h1.
  reflexivity.
Qed.

(* hd_error *)

Inductive natoption : Type :=
  | None : natoption
  | Some : nat -> natoption.

Definition hd_error (l : natlist) : natoption :=
  match l with
    | nil => None
    | cons x xs => Some x
  end.

(* option_elim_hd *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | nil       => default
    | cons x xs => x
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
    | None    => d
    | Some n' => n'
  end.

Theorem option_elim_hd :
  forall (l : natlist) (default : nat), hd default l = option_elim default (hd_error l).
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl; reflexivity.
Qed.

End Natlist.

(* beq_id_refl *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id x1 x2 :=
  match x1, x2 with
    | Id a, Id b => beq_nat a b
  end.

Theorem beq_id_refl :
  forall x, true = beq_id x x.
Proof.
  assert (n_eq_refl : forall n : nat, true = (n =? n)).
  + induction n; trivial.
  + induction x; simpl; apply n_eq_refl.
Qed.

Module PartialMap.
Import Natlist.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d : partial_map) (key : id) (value : nat) :=
  record key value d.

Fixpoint find (x : id) (d : partial_map) {struct d} : natoption :=
  match d with
    | empty         => None
    | record k v d' => match beq_id x k with
      | true  => Some v
      | false => find x d'
    end
  end.

(* update_eq *)

Theorem update_eq :
  forall d k v, find k (update d k v) = Some v.
Proof.
  induction d.
  + simpl.
    intros k.
    rewrite <- (beq_id_refl k).
    reflexivity.
  + simpl.
    intros k.
    rewrite <- (beq_id_refl k).
    reflexivity.
Qed.

(* update_neq *)

Theorem update_neq :
  forall d m n o, beq_id m n = false -> find m (update d n o) = find m d.
Proof.
  induction d.
  + simpl.
    intros m n o h1.
    rewrite h1.
    reflexivity.
  + simpl.
    intros m n' o h1.
    rewrite h1.
    reflexivity.
Qed.

End PartialMap.

(* baz_num_elts *)

Inductive baz : Type :=
  | baz1 : baz -> baz
  | baz2 : baz -> bool -> baz.

(* The type "baz" has no element. *)

Theorem baz_empty :
  forall x : baz, False.
Proof.
  intros x.
  induction x; trivial.
Qed.

