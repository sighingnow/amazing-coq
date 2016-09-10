(* Code for Software Foundations, Chapter 5: Poly: Polymorphism and Higher-Order Functions *)

Require Import Arith.
Require Import List.

(* mumble_grumble *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (T : Type) : Type :=
  | d : mumble -> grumble T
  | e : T -> grumble T.

(* Which of the following are well-typed elements of grumble X for some type X ?
  d (b a 5)        : F
  d mumble (b a 5) : T
  d bool (b a 5)   : T
  e bool true      : T
  e mumble (b c 0) : T
  e bool (b c 0)   : F
  c                : T
*)

End MumbleGrumble.

(* poly_exercises *)

Theorem app_nil_r :
  forall X : Type, forall l : list X, l ++ nil = l.
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl.
    pattern l at 2.
    rewrite IHl.
    reflexivity.
Qed.

Theorem app_nil_l :
  forall X : Type, forall l : list X, nil ++ l = l.
Proof.
  reflexivity.
Qed.

Lemma cons_injection :
  forall (A : Type) (n : A) (l1 l2 : list A), l1 = l2 -> n :: l1 = n :: l2.
Proof.
  intros A n l1 l2.
  induction l1, l2.
  + simpl; reflexivity.
  + inversion 1.
  + inversion 1.
  + intros h1; rewrite h1; reflexivity.
Qed.

Theorem app_assoc :
  forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l, m.
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl; rewrite app_nil_r; reflexivity.
  + simpl.
    intros n.
    apply (cons_injection A a (l ++ a0 :: m ++ n) ((l ++ a0 :: m) ++ n)).
    rewrite <- IHl; trivial.
Qed.

Theorem app_length :
  forall (X : Type) (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1.
  + simpl; reflexivity.
  + simpl; rewrite IHl1; reflexivity.
Qed.

(* more_poly_exercises *)

Theorem rev_app_distr :
  forall (X : Type) (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1, l2.
  + simpl; reflexivity.
  + simpl; rewrite app_nil_r; reflexivity.
  + simpl; repeat rewrite app_nil_r; reflexivity.
  + simpl.
    rewrite app_assoc.
    rewrite IHl1.
    assert(app_xs_r : forall (l1 l2 l3 : list X), l1 = l2 -> l1 ++ l3 = l2 ++ l3).
    - intros l1' l2' l3' h1.
      rewrite h1; reflexivity.
    - apply app_xs_r.
      apply app_xs_r.
      simpl; reflexivity.
Qed.

Theorem rev_involutive :
  forall (X : Type) (l : list X), rev (rev l) = l.
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl.
    rewrite rev_app_distr.
    rewrite IHl.
    simpl; reflexivity.
Qed.

(* combine_checks *)

(*
Check @combine.
Eval compute in combine (1::2::nil) (false::false::true::true::nil).
*)

(* split *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | nil        => (nil, nil)
    | (a, b)::xs =>
      let (u, v) := split xs
      in (a::u, b::v)
  end.

(* Eval compute in split ((1, false)::(2, false)::nil). *)

(* hd_error_poly *)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    | nil   => None
    | x::xs => Some x
  end.

(* filter_even_gt7 *)

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) {struct l} : list X :=
  match l with
    | nil   => nil
    | x::xs => let rest := filter test xs
      in match test x with
        | true  => x :: rest
        | false => rest
      end
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (Nat.even x) (Nat.ltb 7 x)) l.

(* partition *)

Definition partition {X : Type} (test : X -> bool) (l : list X) : (list X) * (list X) :=
  ((filter test l), filter (fun x => negb (test x)) l).

(* map_rev *)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) {struct l} : list Y :=
  match l with
    | nil   => nil
    | x::xs => f x :: map f xs
  end.

Lemma map_append_eq :
  forall (X Y : Type) (f : X -> Y) (l1 l2 : list X), map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1.
  + simpl; reflexivity.
  + simpl; rewrite IHl1; reflexivity.
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl.
    rewrite map_append_eq.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

(* flat_map *)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) {struct l} : list Y :=
  match l with
    | nil   => nil
    | x::xs => f x ++ flat_map f xs
  end.

Definition option_map {X Y : Type} (f : X -> Y) (x : option X) : option Y :=
  match x with
    | None    => None
    | Some x' => Some (f x')
  end.

(* fold_types_different *)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (a : Y) : Y :=
  match l with
    | nil   => a
    | x::xs => f x (fold f xs a)
  end.

(* The type X and Y are different:
  X: nat
  Y: bool. *)
Definition all_even (xs : list nat) : bool :=
  fold (fun x acc => andb acc (Nat.even x)) xs true.

(* fold_length *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ acc => S acc) l O.

Theorem fold_length_correct :
  forall (X : Type) (l : list X), fold_length l = length l.
Proof.
  induction l.
  + reflexivity.
  + simpl.
    rewrite <- IHl.
    reflexivity.
Qed.

(* fold_map *)

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x acc => f x :: acc) l nil.

Theorem fold_map_correct :
  forall (X Y : Type) (f : X -> Y) (l : list X), fold_map f l = map f l.
Proof.
  induction l.
  + simpl; reflexivity.
  + simpl; rewrite <- IHl.
    reflexivity.
Qed.

(* currying *)

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
  f (x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (t : X * Y) : Z :=
  match t with
    | (x, y) => f x y
  end.

Theorem uncurry_curry :
  forall (X Y Z : Type) (f : X -> Y -> Z) x y, prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry :
  forall (X Y Z : Type) (f : (X * Y) -> Z) t, prod_uncurry (prod_curry f) t = f t.
Proof.
  induction t.
  simpl; reflexivity.
Qed.

(* church_numerals *)

Module Church.

Definition church :=
  forall X : Type, (X -> X) -> (X -> X).

(* zero *)
Definition zero : church :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(* one *)
Definition one : church :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(* two *)
Definition two : church :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* three *)
Definition three : church :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

(* succ n *)
Definition succ (n : church) : church :=
  fun (X : Type) (f : X -> X) (x : X) => f ((n X f) x).

(* n + m *)
Definition plus (n m : church) : church :=
  fun (X : Type) (f : X -> X) (x : X) => (m X f) ((n X f) x).

(* n * m *)
Definition mult (n m : church) : church :=
  fun (X : Type) (f : X -> X) => m X (n X f).

(* n ^ m *)
Definition exp (n m : church) : church :=
  fun (X : Type) => (m (X -> X)) (n X).

(*
Eval compute in exp two three.
Eval compute in exp three two.
*)

End Church.

Module ChurchWithFold.

(* TODO : how to represent church numerals in Coq as the paper:
  <Church numerals, Twice!>. *)

End ChurchWithFold.


