(* Code for Coq'Art, Chapter 8: Inductive Predicates. *)

Section InductivePredicates.

Require Import Arith.
Require Import ZArith.
Require Import List.

(* Examples *)
Section Examples.

Inductive plane : Set :=
  | point : Z -> Z -> plane.

Inductive south_west : plane -> plane -> Prop :=
  | south_west_define :
    forall a1 a2 b1 b2 : Z, (a1 < b1) % Z -> (a2 < b2) % Z -> south_west (point a1 b1) (point a2 b2).

Inductive even : nat -> Prop :=
  | even_base : even O
  | even_ss :
    forall n : nat, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
  | odd_base : odd (S O)
  | odd_ss :
    forall n : nat, odd n -> odd (S (S n)).

Inductive sorted (A : Set) (R : A -> A -> Prop) : list A -> Prop :=
  | sorted_nil : sorted A R nil
  | sorted_singleton :
    forall x : A, sorted A R (cons x nil)
  | sorted_all :
    forall (x t : A) (l : list A), R x t -> sorted A R (cons t l) -> sorted A R (cons x (cons t l)).

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S :
    forall m : nat, le n m -> le n (S m).

Definition relation (A : Type) := A -> A -> Prop.

Inductive trans_closure (A : Type) (R : relation A) : A -> A -> Prop :=
  | t_base :
    forall a b : A, R a b -> trans_closure A R a b
  | t_trans :
    forall a b c : A, trans_closure A R a b -> trans_closure A R b c -> trans_closure A R a c.

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 8.1 The last element of a list. *)

Section LastOfList.

Set Implicit Arguments.

Variables A : Set.

Inductive last : A -> list A -> Prop :=
  | last_hd :
    forall a : A, last a (a :: nil)
  | last_tl :
    forall (a b : A) (l : list A), last a l -> last a (b :: l).

Fixpoint last_fun (l : list A) : option A :=
  match l with
    | nil      => None
    | (a::nil) => Some a
    | (_::xs)  => last_fun xs
  end.

Lemma last_fun_tail :
  forall (a b : A) (l : list A), last_fun (a::b::l) = last_fun (b::l).
Proof.
  trivial.
Qed.

Theorem last_fun_correct_some :
  forall (a : A) (l : list A), last a l <-> last_fun l = Some a.
Proof.
  split.
  + intros h1.
    induction h1.
      - simpl; trivial.
      - simpl; rewrite IHh1; induction l;
          [ inversion IHh1
          | trivial
          ].
  + elim l.
    - simpl. discriminate 1.
    - intros a0 l0.
      induction l0.
      * simpl. injection 2.
        intros h1; rewrite h1. apply last_hd.
      * intros h1 h2.
        apply last_tl.
        apply h1.
        rewrite last_fun_tail in h2; apply h2.
Qed.

Lemma last_fun_cons_not_none :
  forall (a : A) (l : list A), last_fun (a :: l) <> None.
Proof.
  intros a l.
  generalize dependent a.
  induction l.
    - discriminate.
    - simpl; intros a'; apply IHl.
Qed.

Hint Resolve last_hd last_tl.

Theorem last_fun_correct_none :
  forall (a : A) (l : list A), last_fun l = None -> ~ last a l.
Proof.
  induction l.
  simpl. inversion 2.
  elim l.
    - inversion 1.
    - intros a' h1 h2 h3 h4.
      apply last_fun_cons_not_none with (a := a) (l := (a0 :: a' :: h1)).
      apply h3.
Qed.

End LastOfList.

(* Exercise 8.2 On palindromes. *)

Section Palidrome.

Set Implicit Arguments.

Variables A : Set.

Inductive remove_last (a : A) : list A -> list A -> Prop :=
  | remove_hd :
    remove_last a (a :: nil) nil
  | remove_tl :
    forall x l1 l2, remove_last a l1 l2 -> remove_last a (x::l1) (x::l2).

Inductive palindromic : list A -> Prop :=
  | nil_pal :
    palindromic nil
  | singleton_pal :
    forall a, palindromic (a::nil)
  | cons_pal :
    forall a l1 l2, palindromic l1 -> remove_last a l2 l1 -> palindromic (a::l2).

Theorem palindromic_rev_eq :
  forall l, palindromic l -> rev l = l.
Proof.
  intros l h1.
  induction h1.
  induction l.
  + trivial.
  +
Qed.

End Palidrome.

End Exercises.

End InductivePredicates.
