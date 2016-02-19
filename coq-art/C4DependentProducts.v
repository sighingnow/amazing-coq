(* Code for Coq Art, Chapter 4: Dependent Products or Pandora's Box. *)

Section DependentProducts.

Require Import Arith.
Require Import ZArith.
Require Import ZArithRing.
Require Import List.

(* The difference:
  Parameters: global declaration.
  Variables: local declaration. *)

Parameters
  (prime_divisor : nat -> nat)
  (prime : nat -> Prop)
  (divides : nat -> nat -> Prop).

(* Examples *)
Section Examples.

Open Scope nat_scope.
Check (prime (prime_divisor 220)).
Check (divides (prime_divisor 220) 220).
(* Partial application, curry. *)
Check (divides 3).

Parameters binary_word : nat -> Set.
Definition short : Set := binary_word 16.
Definition int : Set := binary_word 32.
Definition long : Set := binary_word 64.

Check not (prime 220).

Check
  let d := prime_divisor 220
  in prime d /\ divides d 220.

Parameters (decomp1 : nat -> list nat).
(* In Coq, '*' operator means product, A * B = prod A B. *)
Parameters (decomp2 : nat -> nat * nat).
Check decomp1 220.
Check decomp2 220.

(* For every natural number n, if 2 <= n, then "prime_divisor" returns a
  prime divisor of n. *)
Parameters prime_divisor_spec :
  forall n : nat, 2 <= n -> prime (prime_divisor n) /\ divides (prime_divisor n) n.

Parameters prime_divisor_correct :
  forall n : nat, 2 <= n ->
    let d := prime_divisor n
    in prime d /\ divides d n.
Check prime_divisor_correct.
Check prime_divisor_correct 220.

(* If one concatenates a word of length n with a word of length p, the result must
  have length n+p. *)
Parameters binary_word_concat :
  forall n p : nat, binary_word n -> binary_word p -> binary_word (n+p).

Check cons.
Check pair.
Check fst.
Check snd.
Check
  forall A B : Set, A -> B -> A * B.

Check le_n.
Check le_S.

Check (le_n 36).

Definition le_36_37 := le_S 36 36 (le_n 36).
Check le_36_37.
Definition le_36_38 := le_S 36 37 (le_S 36 36 (le_n 36)). (* le_S 36 36 le_36_37 *)
Check le_36_38.

(* auto type inference, apply the function le_S multiple times on (le_n n). *)
Check (le_S _ _ (le_S _ _ (le_S _ _ (le_n 36)))).

(* iterator a unary function from a type to itself. *)
Parameters iterate_decl :
  forall A : Set, (A -> A) -> nat -> A -> A.
Fixpoint iterate (A : Set) (f : A -> A) (n : nat) (x : A) : A :=
  match n with
    | O => x
    | S p => f (iterate A f p x)
  end.

Check iterate nat.

Check iterate _ (mult 2).
Check iterate _ (mult 2) 10.
Check iterate _ (mult 2) 10 1.
Eval compute in (iterate _ (mult 2) 10 1).

Check binary_word_concat 32.
Check binary_word_concat 32 32.
(* won't be reduced to binary_word 64 here !!!
  zeta-reduction is needed, but only delta-reduction is done. *)

Definition binary_word_dup (n : nat) (w : binary_word n) : binary_word (n+n) :=
  binary_word_concat _ _ w w.

Theorem le_SS :
  forall i : nat, i <= S (S i).
Proof (fun i : nat => le_S _ _ (le_S _ _ (le_n i))).

Definition compose : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C :=
  fun A B C f g x => g (f x).
Check compose.
Print compose.

Check fun (A : Set) (f : Z -> A) => compose _ _ _ Z_of_nat f.
Check compose _ _ _ Zabs_nat (plus 78) 45%Z.

Check le_SS 1515.
Check le_S _ _ (le_SS 1515).

Check iterate _ (fun x => x) 23.

Implicit Arguments compose [A B C].

Set Implicit Arguments.
Definition thrice (A : Set) (f : A -> A) :=
  compose f (compose f f).
Unset Implicit Arguments.

Print compose.
Print thrice.

Eval cbv beta delta in (thrice (thrice (A := nat) S) 0).

Definition short_concat : short -> short -> int :=
  binary_word_concat 16 16.

Check forall i : nat, i <= S (S i).
Check forall n p : nat, binary_word n -> binary_word p -> binary_word (n+p).

(* Nested product types.
  Simultaneous use of dependent types on data types and propositions. *)
Check forall n : nat, 0 < n -> nat.

Check iterate.

Definition my_plus : nat -> nat -> nat :=
  iterate nat S.
Definition my_mult (n p : nat) : nat :=
  iterate nat (my_plus n) p 0.
Definition my_expo (x n : nat) : nat :=
  iterate nat (my_mult x) n 1.

(* The Ackermann function can't be expressed as primitive recursive function. *)
Definition ackermann (n : nat) : nat -> nat :=
  iterate (nat -> nat)
    (fun (f : nat -> nat) (p : nat) => iterate nat f (S p) 1)
    n S.

Eval compute in ackermann 3 5.

Check forall P : Prop, P -> P.
Check fun (P : Prop) (p : P) => p.

(* Equality is reflexive. *)
Check refl_equal.

Theorem ThirtySix : 9 * 4 = 6 * 6.
Proof (refl_equal 36).

Check conj.
Check or_introl.
Check or_intror.

Check and_ind.

Theorem conj3 :
  forall P Q R : Prop, P -> Q -> R -> P /\ Q /\ R.
Proof fun P Q R p q r => conj p (conj q r).

Theorem disj4_3 :
  forall P Q R S : Prop, R -> P \/ Q \/ R \/ S.
Proof.
  exact (fun P Q R S r => or_intror _ (or_intror _ (or_introl _ r))).
Qed.

Definition proj :
  forall A B : Prop, A /\ B -> A :=
    fun (A B : Prop) (h : A /\ B) => and_ind (fun (a : A) (_ : B) => a) h.
Print proj.

Check ex (fun z : nat => z * z <= 37 /\ 37 < (z+1)*(z+1)).

Check ex_intro.
Check ex_ind.

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 4.1 Some types in the calculus of constructions. *)

Check fun f : nat -> nat => forall n: nat, f n = n.
Check fun f g : nat -> nat => forall n: nat, f n = g n.
Check fun a b : nat => a = b.

(* Exercise 4.2 Polymorphic functions and implicit arguments. *)

(** The implicit type: nat. **)

(* Exercise 4.3 Construct terms inhabits types. *)

Section A_Declared.

Variables
  (A : Set)
  (P Q : A -> Prop)
  (R : A -> A -> Prop).

Theorem all_perm : (
  forall a b : A, R a b) ->
    forall a b : A, R b a.
Proof.
  intros h1.
  intros v1 v2.
  apply h1.
Qed.
Print all_perm.

Theorem all_imp_dist : (
  forall a b : A, P a -> Q a) -> (
    forall a : A, P a) ->
      forall a : A, Q a.
Proof.
  intros h1 h2.
  intros v1.
  apply h1.
  apply v1.
  apply h2.
Qed.

Theorem all_delta : (
  forall a b : A, R a b) ->
    forall a : A, R a a.
Proof.
  intros h1.
  intros v1.
  apply h1.
Qed.
Print all_delta.

End A_Declared.

(* Exercise 4.4 Construct terms inhabits types and realize specifications. *)

Theorem id :
  forall A : Set, A -> A.
Proof fun (A : Set) (a : A) => a.

Theorem diag :
  forall A B : Set, (A -> A -> B) -> A -> B.
Proof fun (A B : Set) (f : A -> A -> B) (a : A) => f a a.

Theorem permute :
  forall A B C : Set, (A -> B -> C) -> B -> A -> C.
Proof fun (A B C : Set) (f : A -> B -> C) (b : B) (a : A) => f a b.

Theorem f_nat_Z :
  forall A : Set, (nat -> A) -> Z -> A.
Proof fun (A : Set) (f : nat -> A) (z : Z) => f (Zabs_nat z).

Theorem f_nat_Z' :
  forall A : Set, (nat -> A) -> Z -> A.
Proof.
  intros SA h1 h2.
  apply h1.
  (* Use "constructor" tactic to do the type casting. *)
  constructor.
Qed.
Print f_nat_Z'.

(* Exercise 4.5 Construct terms inhabits types. *)

Theorem all_perm' :
  forall (A : Type) (P : A -> A -> Prop), (
    forall (x y : A), P x y) ->
      forall (x y : A), P y x.
Proof.
  intros h1 h2 h3 h4 h5.
  apply h3.
Qed.
Print all_perm'.

Theorem resolution :
  forall (A : Type) (P Q R S : A -> Prop), (
    forall (a : A), Q a -> R a -> S a) -> (
      forall (b : A), P b -> Q b) -> (
        forall (c : A), P c -> R c -> S c).
Proof.
  intros t p q r s h1 h2.
  intros value.
  intros h3 h4.
  apply h1; [apply h2; apply h3 | apply h4].
Qed.
Print resolution.

End Exercises.

End DependentProducts.
