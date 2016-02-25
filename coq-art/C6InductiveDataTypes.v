(* Code for Coq Art, Chapter 6: Inductive Data Types. *)

Section InductiveDataTypes.

Require Import Arith.
Require Import ZArith.
Require Import List.

(* Examples *)
Section Examples.

Print bool.

Inductive month : Set :=
  | January | February | March | April | May | June
  | July | August | September | Octomber | November | December.

Check month_ind.
Check month_rec.
Check month_rect.

Theorem month_equal :
  forall m : month, m = January \/ m = February \/ m = March \/ m = April \/ m = May \/ m = June
    \/ m = July \/ m = August \/ m = September \/ m = Octomber \/ m = November \/ m = December.
Proof.
  (* or use "induction m; auto 12." *)
  intros m.
  (* "elim t" is equivalant to "pattern t; apply T_ind.". *)
  pattern m; apply month_ind; auto 12.

  (* Another ways to prove this proposition. *)
  (* "induction m; auto 12." *)
  (* "intros m; elim m; auto 12." *)
Qed.
Print month_equal.

Check fun b : bool =>
  match b with
    | true => 33
    | false => 45
  end.

Definition month_length (leap (* leap year *) : bool) : month -> nat :=
  month_rec (fun m : month => nat)
    31 (if leap then 29 else 28) 31 30 31 30 31 31 30 31 30 31.

Definition month_length' (leap : bool) (m : month) : nat :=
  match m with
    | January   => 31
    | February  => if leap then 29 else 28
    | March     => 31
    | April     => 30
    | May       => 31
    | June      => 30
    | July      => 31
    | August    => 31
    | September => 30
    | Octomber  => 31
    | November  => 30
    | December  => 31
  end.

Definition month_length'' (leap : bool) (m : month) : nat :=
  match m with
    | February  => if leap then 29 else 28
    | April     => 30
    | June      => 30
    | September => 30
    | November  => 30
    | _         => 31 (* Default clauses. *)
  end.

Theorem length_feb : month_length false February = 28.
Proof.
  simpl.
  trivial.
Qed.

(* Inductive plane : Set :=
  | point : Z -> Z -> plane.
Definition abscissa (p : plane) : Z :=
  match p with point x _ => x end.
Definition ordinate (p : plane) : Z :=
  match p with point _ y => y end. *)

Record plane : Set := point {
  abscissa : Z;
  ordinate : Z
}.

Inductive vehicle : Set :=
  | bicycle : nat -> vehicle
  | motorcycle : nat -> nat -> vehicle.

Check vehicle_ind.

Definition nb_wheels (v : vehicle) : nat :=
  match v with
    | bicycle _           => 2
    | motorcycle _ wheels => wheels
  end.

Definition nb_seats (v : vehicle) : nat :=
  match v with
    | bicycle seats      => seats
    | motorcycle seats _ => seats
  end.

Theorem at_least_28 :
  forall (leap : bool) (m : month), 28 <= month_length leap m.
Proof.
  intros leap m.
  (* case leap, m; simpl; repeat (trivial; apply le_S). *)
  case m; simpl; repeat (trivial; apply le_S).
  case leap; simpl; (trivial; apply le_S; trivial).
Qed.
Print at_least_28.

Definition next_month : month -> month :=
  month_rec (fun m : month => month)
    February March April May June July
    August September Octomber November December January.

Theorem jan_neq_feb :
  January <> February.
Proof.
  discriminate.
  (* Another solution: "intros h1; discriminate h1.". *)
Qed.

Theorem jan_neq_feb' :
  January <> February.
Proof.
  intros h1.
  change ((fun m : month =>
    match m with
      | January => True
      | _       => False
    end) February).
  rewrite <- h1; trivial.
Qed.

Theorem next_auguest_then_july :
  forall m : month, next_month m = August -> m = July.
Proof.
  intros m.
  case m; simpl; intros h1; discriminate h1 || reflexivity.
Qed.

Theorem bicycle_same_seats :
  forall s1 s2 : nat, bicycle s1 = bicycle s2 -> s1 = s2.
Proof.
  intros s1 s2 h1.
  injection h1; trivial.
Qed.

Theorem bicycle_same_seats' :
  forall s1 s2 : nat, bicycle s1 = bicycle s2 -> s1 = s2.
Proof.
  intros s1 s2 h1.
  change (nb_seats (bicycle s1) = nb_seats (bicycle s2)).
  rewrite h1; trivial.
Qed.

Theorem bicycle_same_seats'' :
  forall s1 s2 : nat, bicycle s1 = bicycle s2 -> s1 = s2.
Proof.
  intros s1 s2 h1.
  change (
    let
      get_seats := vehicle_rec (fun v : vehicle => nat)
        (fun s => s)
        (fun s _ => s)
    in get_seats (bicycle s1) = get_seats (bicycle s2)).
  rewrite h1; reflexivity.
Qed.

Section InjectionExample.

Variable A B : Set.
Inductive T : Set :=
  | c1 : A -> T
  | c2 : B -> T.

Theorem inject_c2 :
  forall x y : B, c2 x  = c2 y -> x = y.
Proof.
  intros x y h1.
  change (
    let
      phi := fun v : T =>
        match v with
          | c1 _  => x
          | c2 v' => v'
        end
    in phi (c2 x) = phi (c2 y)).
  rewrite h1; reflexivity.
Qed.

End InjectionExample.

Theorem next_march_shorter :
  forall (leap : bool) (m1 m2 : month), next_month m1 = March -> month_length leap m1 <= month_length leap m2.
Proof.
  intros leap m1 m2.
  case leap, m1, m2; simpl;
  trivial || discriminate || idtac;
  intros; repeat (apply le_S; trivial).
Qed.

Theorem next_march_shorter' :
  forall (leap : bool) (m1 m2 : month), next_month m1 = March -> month_length leap m1 <= month_length leap m2.
Proof.
  intros leap m1 m2 h1.
  generalize h1.
  case m1;
    discriminate ||
    case leap; case m2; simpl; intros; repeat (trivial; apply le_S; trivial).
Qed.

Theorem next_march_shorter'' :
  forall (leap : bool) (m1 m2 : month), next_month m1 = March -> month_length leap m1 <= month_length leap m2.
Proof.
  intros leap m1 m2 h1.
  generalize (refl_equal m1).
  pattern m1 at -1; (* "pattern m1 at 2 3." *) case m1; (intro h2; rewrite h2 in h1; simpl in h1; discriminate h1) || idtac.
  case leap, m2; simpl; intros; repeat (trivial; apply le_S; trivial).
Qed.

(* Same with the standard tactic "case_eq". *)
Ltac case_equal f :=
  generalize (refl_equal f); pattern f at -1; case f.

Theorem next_march_shorter''' :
  forall (leap : bool) (m1 m2 : month), next_month m1 = March -> month_length leap m1 <= month_length leap m2.
Proof.
  intros leap m1 m2 h1.
  case_eq m1; (intro h2; rewrite h2 in h1; simpl in h1; discriminate h1) || idtac.
  case leap, m2; simpl; intros; repeat (trivial; apply le_S; trivial).
Qed.

Check nat_ind.

Theorem plus_assoc :
  forall a b c : nat, (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  (* Eliminate "a" with the induction principle on natural numbers. *)
  elim a.

  rewrite plus_O_n.
  rewrite plus_O_n.
  trivial.

  intros n h1.
  rewrite (plus_Sn_m n b).
  rewrite (plus_Sn_m (n+b) c).
  rewrite (plus_Sn_m n (b+c)).
  rewrite h1.
  trivial.
Qed.

Theorem plus_assoc' :
  forall a b c : nat, a + b + c = a + (b + c).
Proof.
  intros a b c.
  elim a; simpl;
    [ idtac
    | intros n h1;
      rewrite h1
    ];
    trivial.
Qed.

Fixpoint mult2 (n : nat) : nat :=
  match n with
    | O   => O
    | S p => S (S (mult2 p))
  end.

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n with
    | O    => m
    | S n' => S (plus n' m)
  end.

Fixpoint iterate (A : Set) (f : A -> A) (n : nat) (x : A) {struct n} : A :=
  match n with
    | O    => x
    | S n' => f (iterate A f n' x)
  end.

Definition ackermann : nat -> nat -> nat :=
  fun (n : nat) =>
    iterate (nat -> nat)
      (fun (f : nat -> nat) (p : nat) => iterate nat f (S p) 1)
      n S.

Inductive Z_btree : Set :=
  | Z_leaf  : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Fixpoint sum_of_values (t : Z_btree) {struct t} : Z :=
  match t with
    | Z_leaf            => 0
    | Z_bnode value l r => sum_of_values l + value + sum_of_values r
  end.

Fixpoint zero_present (t : Z_btree) {struct t} : bool :=
  match t with
    | Z_leaf        => false
    | Z_bnode 0 _ _ => true
    | Z_bnode _ l r => if zero_present l then true else zero_present r
  end.

Fixpoint positive_succ (x : positive) {struct x} : positive :=
  match x with
    | xH    => xI xH                 (* x = 1 *)
    | xO x' => xI x'                 (* x = x' * 2 *)
    | xI x' => xO (positive_succ x') (* x = x' * 2 + 1 *)
  end.

Eval compute in positive_succ 10.

Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  (* "true" is used to index the first branch, and "false" is used to index the second branch. *)
  | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.


Definition right_son (t : Z_btree) : Z_btree :=
  match t with
    | Z_leaf          => Z_leaf
    | Z_bnode a t1 t2 => t2
  end.

Definition fright_son (t : Z_fbtree) : Z_fbtree :=
  match t with
    | Z_fleaf     => Z_fleaf
    | Z_fnode a f => f false
  end.

Fixpoint fsum_of_values (t : Z_fbtree) {struct t} : Z :=
  match t with
    | Z_fleaf     => 0 % Z
    | Z_fnode v f => fsum_of_values (f true) + v + fsum_of_values (f false)
  end.

Inductive Z_inf_tree : Set :=
  | Z_inf_leaf : Z_inf_tree
  (* The branches are indexed with the natural numbers. *)
  | Z_inf_node : Z -> (nat -> Z_inf_tree) -> Z_inf_tree.

Fixpoint nsum_of_values (n : nat) (t : Z_inf_tree) {struct t} : Z :=
  match t with
    | Z_inf_leaf     => 0 % Z
    | Z_inf_node v f =>
      let sum_f :=
        fix sum_f_helper (n : nat) (f : nat -> Z) {struct n} : Z :=
          match n with
            | O => f O
            | S n' => Zplus (f n') (sum_f_helper n' f)
          end
      in v + sum_f n (fun x : nat => nsum_of_values n (f x))
  end.

Print list.
Section define_lists.
Variable A : Set.
Inductive list' : Set :=
  | nil'  : list'
  | cons' : A -> list' -> list'.
End define_lists.


Fixpoint app' (A : Set) (l1 l2 : list' A) {struct l1} : list' A :=
  match l1 with
    | nil' _ => l2
    | cons' _ x xs => cons' _ x (app' A xs l2)
  end.

Print option.

Definition pred_option (n : nat) : option nat :=
  match n with
    | O    => None
    | S n' => Some n'
  end.

Definition pred_pred_option (n : nat) : option nat :=
  match pred_option n with
    | None    => None
    | Some n' => pred_option n'
  end.

Check nth.

Fixpoint nth_option (A : Set) (n : nat) (l : list A) {struct l} : option A :=
  match n, l with
    | O, x::_    => Some x
    | S p, _::xs => nth_option A p xs
    | _, nil     => None
  end.
Implicit Arguments nth_option [A].

Fixpoint nth_option' (A : Set) (n : nat) (l : list A) {struct n} : option A :=
  match n, l with
    | O, x::_    => Some x
    | S p, _::xs => nth_option' A p xs
    | _, nil     => None
  end.
Implicit Arguments nth_option' [A].

Check (sum nat bool).
Check (inl bool 5).
Check (inr bool false).

Inductive ltree (n : nat) : Set :=
  | lleaf : ltree n
  | lnode :
    forall p : nat, p <= n -> ltree n -> ltree n -> ltree n.

Inductive sqrt_data (n : nat) : Set :=
  | sqrt_prop :
    forall x : nat, x * x <= n -> x < (S x) * (S x) -> sqrt_data n.

Inductive htree (A : Set) : nat -> Set :=
  | hleaf : A -> htree A O
  | hnode :
    forall n : nat, A -> htree A n -> htree A n -> htree A (S n).

Check htree_ind.

Fixpoint htree_to_tree (n : nat) (t : htree Z n) {struct t} : Z_btree :=
  match t with
    | hleaf _ v       => Z_bnode v Z_leaf Z_leaf
    | hnode _ h v l r => Z_bnode v (htree_to_tree h l) (htree_to_tree h r)
  end.

(* Get the mirror image of fixed-height tree "t". *)
Fixpoint invert (A : Set) (n : nat) (t : htree A n) {struct t} : htree A n :=
  match t in htree _ v return htree A v with
    | hleaf _ v => hleaf A v
    | hnode _ h v l r => hnode A h v (invert A h r) (invert A h l)
  end.

Print Empty_set.
Check Empty_set_ind.

Inductive strange : Set :=
  | constructor : strange -> strange.
Check strange_ind.

Theorem strange_empty :
  forall x : strange, False.
Proof.
  intros x.
  induction x.
  apply IHx.
Qed.

Inductive evens : nat -> Set :=
  | even_origin  : evens O
  | even_iterate :
    forall n : nat, evens n -> evens (S (S n)).

Check evens.
Check evens_ind.
Check even_origin.
Check even_iterate _ even_origin.
Check even_iterate _ (even_iterate _ even_origin).

End Examples.

(* Exercises. *)
Section Exercises.

(* Exercise 6.1 On seasons. *)

Inductive season : Set :=
  | Spring | Summer | Autumn | Winter.

Definition month_in_season : month -> season :=
  (* NOTE the usage of "month_rec" is important ! *)
  month_rec (fun _ => season)
    Spring Spring Spring Summer Summer Summer
    Autumn Autumn Autumn Winter Winter Winter.

(* Exercise 6.2 *)

Print bool.
Check bool_ind.
Check bool_rec.
Check bool_rect.

(* Exercise 6.3 Using "bool_ind". *)

Check bool_ind.

Theorem bool_equal :
  forall b : bool, b = true \/ b = false.
Proof.
  induction b; auto 2.
Qed.

Theorem bool_equal' :
  forall b : bool, b = true \/ b = false.
Proof.
  intros b.
  pattern b. apply bool_ind; [left | right]; reflexivity.
Qed.

Theorem bool_equal'' :
  forall b : bool, b = true \/ b = false.
Proof.
  apply (bool_ind (fun b : bool => b = true \/ b = false)
    (or_introl _ (refl_equal true))
    (or_intror _ (refl_equal false))).
Qed.

(* Exercise 6.4 On seasons (continued). *)

Definition month_in_season' (m : month) : season :=
  match m with
    | January   => Spring
    | February  => Spring
    | March     => Spring
    | April     => Summer
    | May       => Summer
    | June      => Summer
    | July      => Autumn
    | August    => Autumn
    | September => Autumn
    | Octomber  => Winter
    | November  => Winter
    | December  => Winter
  end.

(* Exercise 6.5 *)

(* Print Init.Nat.even.

Init.Nat.even = 
fix even (n : nat) :
  bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => even n'
  end
     : nat -> bool *)

Definition month_length_even (leap : bool) (m : month) : bool :=
  Init.Nat.even (month_length leap m).

(* Exercise 6.6 Computing on booleans. *)

Definition bool_not (b : bool) : bool :=
  match b with
    | true  => false
    | false => true
  end.
Definition bool_and (b1 b2 : bool) : bool :=
  if b1 then b2 else b1.
Definition bool_or (b1 b2 : bool) : bool :=
  if b1 then b1 else b2.
Definition bool_xor (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true   => false
    | false, false => false
    | _, _         => true
  end.
Definition bool_eq (b1 b2 : bool) : bool :=
  bool_not (bool_xor b1 b2).

Theorem bool_xor_not_eq :
  forall b1 b2 : bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
  intros b1 b2; case b1, b2; simpl; trivial.
Qed.

Theorem de_morgan_not_and :
  forall b1 b2 : bool, bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2; case b1, b2; simpl; trivial.
Qed.

Theorem bool_double_not :
  forall b : bool, bool_not (bool_not b) = b.
Proof.
  intros b; case b; simpl; trivial.
Qed.

Theorem bool_excluded_middle :
  forall b : bool, bool_or b (bool_not b) = true.
Proof.
  intros b; case b; simpl; trivial.
Qed.

Theorem bool_eq_reflect :
  forall b1 b2 : bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  intros b1 b2.
  case b1, b2; simpl;
    [ idtac
    | intros h1; elim h1
    | idtac
    | idtac
    ]; trivial.
Qed.

Theorem bool_eq_reflect' :
  forall b1 b2 : bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  intros b1 b2 h1.
  rewrite h1; case b2; simpl; trivial.
Qed.

Theorem bool_eq_reflect'' :
  forall b1 b2 : bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  intros b1 b2.
  case b1, b2; simpl;
    [ trivial
    | discriminate (* The hypothesis of this goal is a contradictory equalities. *)
    | discriminate (* The hypothesis of this goal is a contradictory equalities. *)
    | trivial
    ].
Qed.

Theorem de_morgan_not_or :
  forall b1 b2 : bool, bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2; case b1, b2; simpl; trivial.
Qed.

Theorem bool_distr :
  forall b1 b2 b3 : bool, bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
Proof.
  intros b1 b2 b3; case b1, b2, b3; simpl; trivial.
Qed.

(* Exercise 6.7 *)

(* Record plane : Set := point {
  abscissa : Z;
  ordinate : Z
}. *)
(* The type of "plane_rec":
  plane_rec :
    forall P : plane -> Set, (
      forall abscissa ordinate : Z, P (point abscissa ordinate)) ->
        forall p : plane, P p
*)

(* Exercise 6.8 Manhattan distance. *)

(* Record plane : Set := point {
  abscissa : Z;
  ordinate : Z
}. *)
Definition manhattan_distance (P Q : plane) : Z :=
  (Zabs (abscissa P - abscissa Q)) + (Zabs (ordinate P - ordinate Q)).

(* Exercise 6.9 Functions defined by cases without "match". *)

(* Inductive vehicle : Set :=
  | bicycle : nat -> vehicle
  | motorcycle : nat -> nat -> vehicle. *)

Check vehicle_rec.

Definition nb_seats' : vehicle -> nat :=
  (* NOTE The usage of "T_rec" for constructors of inductive data type. *)
  vehicle_rec (fun v: vehicle => nat)
    (fun seats => seats)
    (fun seats wheels => seats).

(* Exercise 6.10 Applying "mont_rect". *)

Definition is_january : month -> Prop :=
  month_rect (fun m : month => Prop)
    False True False False False False
    False False False False False False.

(* Exercise 6.11 A manual proof of discrimination. *)

Theorem true_neq_false :
  true <> false.
Proof.
  intros h1.
  change ((fun b : bool =>
    match b with
      | true  => True
      | _     => False
    end) false).
  rewrite <- h1; trivial.
Qed.

Theorem true_neq_false' :
  true <> false.
Proof.
  discriminate.
Qed.

(* Exercise 6.12 *)

(* Inductive vehicle : Set :=
  | bicycle : nat -> vehicle
  | motorcycle : nat -> nat -> vehicle. *)

Theorem bicycle_neq_motorcycle :
  forall s k w : nat, bicycle s <> motorcycle k w.
Proof.
  intros s k w h1.
  change ((vehicle_rect (fun v : vehicle => Prop) (fun _ => True) (fun _ _ => False)) (motorcycle k w)).
  rewrite <- h1; simpl; trivial.

  (* Simple proof using "discriminate" tactic: "discriminate.". *)
Qed.

(* Exercise 6.13 About the danger of axioms. *)

Record RatPlus : Set := mkRat {
  top : nat;
  bottom : nat;
  bottom_condition : bottom <> 0;
}.

Axiom ratplus_eq :
  forall r r' : RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.

Definition r0 : RatPlus := mkRat 4 6 (not_eq_sym (O_S 5)).
Definition r1 : RatPlus := mkRat 2 3 (not_eq_sym (O_S 2)).

Lemma r0_eq_r1 : r0 = r1.
Proof.
  apply ratplus_eq; simpl; trivial.
Qed.

Lemma r0_neq_r1 : r0 <> r1.
Proof.
  discriminate.
Qed.

Lemma condrad : False.
Proof.
  apply (r0_neq_r1 r0_eq_r1).
Qed.

(* Inconsistent ! *)
Unset ratplus_eq.

(* Exercise 6.14 *)

Fixpoint mult (n m : nat) {struct n} : nat :=
  match n with
    | O    => O
    | S n' => plus m (mult n' m)
  end.

(** The table describing convertibility for simple patterns of the two arguments of "mult":
  (mult O O) => O
  (mult O m) => m
  (mult (S n') O => plus O (mult n' O))
  (mult (S n') m => plus m (mult n' m)) **)

(* Exercise 6.15 Definition by cases. *)

Definition nat_lt_three (n : nat) : bool :=
  match n with
    | O => true
    | 1 => true
    | 2 => true
    | _ => false
  end.

(* Exercise 6.16 Another definition of addition. *)

Fixpoint addition (n m : nat) {struct m} : nat :=
  match m with
    | O    => n
    | S m' => S (addition n m')
  end.

(* Exercise 6.17 Computing $f(0)+f(1)+...+f(n)$. *)

Fixpoint sum_f (f : nat -> Z) (n : nat) {struct n} : Z :=
  match n with
    | O    => f O
    | S n' => Zplus (f n') (sum_f f n')
  end.

(* Exercise 6.18 Computing $2^n.*)

Fixpoint two_power (n : nat) {struct n} : nat :=
  match n with
    | O    => 1
    | S n' => Nat.mul 2 (two_power n')
  end.

Definition two_power' (n : nat) : nat :=
  iterate nat (fun n : nat => Nat.mul n 2) n 1.

Fixpoint two_power_tco (acc n : nat) {struct n} : nat :=
  match n with
    | O    => acc
    | S n' => two_power_tco (Nat.mul acc 2) n'
  end.

(* Exercise 6.19 Representation of positive numbers. *)

Eval compute in xO (xO (xO (xI (xO (xI (xI (xI (xI xH)))))))).
Eval compute in xI (xO (xO (xI xH))).
Eval compute in xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))).

(** In "coqtop":
  Unset Printing Notations.
  Check 1000 % positive.
  Check 25 % positive.
  Check 512 % positive. **)

(* Exercise 6.20 On even positive numbers. *)

Definition pos_even_bool (x : positive) : bool :=
  match x with
    | xH   => true
    | xO _ => false
    | xI _ => true
  end.

(* Exercise 6.21 Division by 4. *)

Definition pos_div4 (x : positive) : Z :=
  match x with
    | xO (xO x') => Zpos x'
    | xO (xI x') => Zpos x'
    | xI (xO x') => Zpos x'
    | xI (xI x') => Zpos x'
    | _          => 0
  end.

(* Exercise 6.22 *)

Definition Zmul_using_pos_mult (a b : Z) : Z :=
  match a, b with
    | Z0, _            => Z0
    | _, Z0            => Z0
    | Zpos a', Zpos b' => Zpos (Pos.mul a' b')
    | Zpos a', Zneg b' => Zneg (Pos.mul a' b')
    | Zneg a', Zpos b' => Zneg (Pos.mul a' b')
    | Zneg a', Zneg b' => Zpos (Pos.mul a' b')
  end.

(* Exercise 6.23 Propositional formulae. *)

Inductive L : Set :=
  | Ltrue        : L
  | Lfalse       : L
  | Ldisjunction : L -> L -> L
  | Lconjunction : L -> L -> L
  | Lnot         : L -> L
  | Limpl        : L -> L -> L.

Fixpoint logic_value (lexpr : L) {struct lexpr} : bool :=
  match lexpr with
    | Ltrue            => true
    | Lfalse           => false
    | Ldisjunction l r => orb (logic_value l) (logic_value r)
    | Lconjunction l r => andb (logic_value l) (logic_value r)
    | Lnot expr        => negb (logic_value expr)
    | Limpl l r        => implb (logic_value l) (logic_value r)
  end.

(* Exercise 6.24 On fractions. *)

(* Inductive definition for positive rational numbers. *)
Inductive RationalF : Set :=
  | vI : RationalF               (* 1 *)
  | vN : RationalF -> RationalF  (* n(x) = 1+x *)
  | vD : RationalF -> RationalF. (* d(x) = \frac{1}{1+\frac{1}{x}} *)

(* Exercise 6.25 Looking for a value in a tree. *)

(* Inductive Z_btree : Set :=
  | Z_leaf  : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree. *)

Fixpoint value_present (value : Z) (t : Z_btree) {struct t} : bool :=
  match t with
    | Z_leaf        => false
    | Z_bnode v l r => orb (orb (Zeq_bool value v) (value_present value l)) (value_present value r)
  end.

Definition zero_present' (t : Z_btree) : bool :=
  value_present (0 % Z) t.

(* Exercise 6.26 Logarithm and power. *)

Fixpoint power (x : Z) (n : nat) {struct n} : Z :=
  match n with
    | O    => 1 % Z
    | S n' => Z.mul x (power x n')
  end.

Print positive.

Fixpoint discrete_log (posn : positive) {struct posn} : nat :=
  match posn with
    | xH    => O
    | xO n' => Nat.add (1 % nat) (discrete_log n')
    | xI n' => Nat.add (1 % nat) (discrete_log n')
  end.

(* Exercise 6.27 Representing trees with functions. *)

(* Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  (* "true" is used to index the first branch, and "false" is used to index the second branch. *)
  | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree. *)

Fixpoint fzero_present (t : Z_fbtree) {struct t} : bool :=
  match t with
    | Z_fleaf     => false
    | Z_fnode 0 _ => true
    | Z_fnode _ f => orb (fzero_present (f true)) (fzero_present (f false))
  end.

Fixpoint fvalue_present (value : Z) (t : Z_fbtree) {struct t} : bool :=
  match t with
    | Z_fleaf     => false
    | Z_fnode v f => orb (Zeq_bool v value) (orb (fvalue_present value (f true)) (fvalue_present value (f false)))
  end.

Definition fzero_present' (t : Z_fbtree) : bool :=
  fvalue_present (0 % Z) t.

(* Exercise 6.28 Finding 0 in an infinitely branching tree. *)

(* Inductive Z_inf_tree : Set :=
  | Z_inf_leaf : Z_inf_tree
  (* The branches are indexed with the natural numbers. *)
  | Z_inf_node : Z -> (nat -> Z_inf_tree) -> Z_inf_tree. *)

Fixpoint nvalue_present (n : nat) (value : Z) (t : Z_inf_tree) {struct t} : bool :=
  match t with
    | Z_inf_leaf     => false
    | Z_inf_node v f =>
      let present_f :=
        fix present_f_helper (n : nat) (f : nat -> bool) {struct n} : bool :=
          match n with
            | O    => f O
            | S n' => orb (f n') (present_f_helper n' f)
          end
      in orb (Zeq_bool v value) (present_f n (fun x : nat => nvalue_present n value (f x)))
  end.

Definition nzero_present (n : nat) (t : Z_inf_tree) : bool :=
  nvalue_present n (0 % Z) t.

(* Exercise 6.29 A simple proof by elimination. *)

Check plus_n_O.

Theorem plus_n_O :
  forall n : nat, n = n + O.
Proof.
  intros n.
  elim n;
    [ simpl; reflexivity
    | intros n' h1;
      simpl;
      rewrite <- h1; reflexivity
    ].
Qed.

(* Exercise 6.30 Representing trees with functions (continued). *)

Section ZBTreeRepresentation.

(* Inductive Z_btree : Set :=
  | Z_leaf  : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  (* "true" is used to index the first branch, and "false" is used to index the second branch. *)
  | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree. *)

Fixpoint f1 (t : Z_btree) {struct t} : Z_fbtree :=
  match t with
    | Z_leaf        => Z_fleaf
    | Z_bnode v l r => Z_fnode v (fun x : bool => if x then (f1 l) else (f1 r))
  end.

Fixpoint f2 (t : Z_fbtree) {struct t} : Z_btree :=
  match t with
    | Z_fleaf     => Z_leaf
    | Z_fnode v f => Z_bnode v (f2 (f true)) (f2 (f false))
  end.

Lemma Z_fnode_equal :
  forall v1 v2 f1 f2, v1 = v2 -> f1 = f2 -> Z_fnode v1 f1 = Z_fnode v2 f2.
Proof.
  intros v1 v2 f1 f2.
  intros h1 h2.
  rewrite h1; rewrite h2; trivial.
Qed.

Lemma Z_fnode_equal_reverse :
  forall v1 v2 f1 f2, Z_fnode v1 f1 = Z_fnode v2 f2 -> v1 = v2 /\ f1 = f2.
Proof.
  intros v1 v2 f1 f2.
  intros h1.
  injection h1.
  intros; split; assumption.
Qed.

Lemma f2_f1_fix :
  forall t : Z_btree, f2 (f1 t) = t.
Proof.
  induction t; simpl;
    [ idtac
    | rewrite IHt1; rewrite IHt2
    ];
    trivial.
Qed.

Hypothesis function_equal :
  forall (A B : Set) (f g : A -> B), (
    forall a, f a = g a) -> f = g.

Lemma f1_f2_fix :
  forall t : Z_fbtree, f1 (f2 t) = t.
Proof.
  induction t; simpl.

  trivial.

  do 2 rewrite H. (* "rewrite H; rewrite H." *)
  rewrite <- (function_equal _ _ (fun x : bool => if x then z0 true else z0 false) z0);
    [ idtac
    | intros a; case a
    ];
    trivial.
Qed.

End ZBTreeRepresentation.

(* Exercise 6.31 A simple proof by induction. *)

(* Fixpoint mult2 (n : nat) : nat :=
  match n with
    | O   => O
    | S p => S (S (mult2 p))
  end. *)

(* Lemma impl_succ_eq :
  forall m n : nat, m = n -> S m = S n.
Proof.
  intros m n h1.
  rewrite h1; reflexivity.
Qed.

Lemma plus_S_m_n :
  forall m n : nat, S (m + n) = m + S n.
Proof.
  intros m n.
  induction m.
  simpl; trivial.
  simpl; rewrite IHm; trivial.
Qed. *)

Theorem mult_2_eq_add :
  forall n : nat, mult2 n = n + n.
Proof.
  induction n.

  simpl; trivial.

  simpl.
  rewrite IHn.
  apply eq_S.
  apply plus_n_Sm.
Qed.

(* Exercise 6.32 On the sum of the n first natural numbers. *)

Fixpoint sum_n (n : nat) :=
  match n with
    | O => O
    | S p => n + sum_n p
  end.

Theorem sum_n_formula :
  forall n : nat, 2 * sum_n n = n * (n + 1).
Proof.
  induction n.

  simpl. reflexivity.

  unfold sum_n; fold sum_n.
  rewrite mult_plus_distr_l.
  rewrite IHn.
  simpl.
  f_equal.
  rewrite plus_n_O.
  rewrite mult_succ_r.
  rewrite mult_plus_distr_l.
  (* TODO *)
Admitted.

(* Exercise 6.33 On the sum of the n first natural numbers. *)

(* Fixpoint sum_n (n : nat) :=
  match n with
    | O => O
    | S p => n + sum_n p
  end. *)

Theorem n_le_sum_n :
  forall n : nat, n <= sum_n n.
Proof.
  induction n.
  simpl; trivial.
  simpl.
  apply le_n_S.
  apply (Nat.le_trans n (n + n), (n + sum_n n)).
  apply (le_plus_l n n).
  apply (plus_le_compat n n n (sum_n n)); [reflexivity | assumption].
Qed.

(* Exercise 6.34 A simple polymorphic function on lists. *)

Definition take_first_two (A : Set) (l : list A) : list A :=
  match l with
    | nil     => nil
    | a::nil  => a::nil
    | b::a::_ => b::a::nil
  end.
Implicit Arguments take_first_two [A].

(* Exercise 6.35 A simple polymorphic function on lists. *)

Fixpoint take (A : Set) (n : nat) (l : list A) {struct n} : list A :=
  match n, l with
    | O, _       => nil
    | _, nil     => nil
    | S p, x::xs => x :: take A p xs
  end.
Implicit Arguments take [A].

(* Exercise 6.36 *)

Fixpoint lsum_of_values (l : list Z) {struct l} : Z :=
  match l with
    | nil   => 0 % Z
    | x::xs => x + lsum_of_values xs
  end.

(* Exercise 6.37 *)

Fixpoint repeat_one_n (n : nat) {struct n} : list nat :=
  match n with
    | O   => nil
    | S p => 1 :: repeat_one_n p
  end.

(* Exercise 6.38 On the list "1::2:: ... n::nil". *)

Definition generate_n_enum (n : nat) : list nat :=
  let helper :=
    fix generate (n c : nat) {struct c} : list nat :=
      match c with
        | O    => nil
        | S c' => n :: generate (S n) c'
      end
  in helper 1 n.

(* Exercise 6.39 *)

(* Fixpoint nth_option'' (A : Set) (n : nat) (l : list A) {struct l} : option A :=
  match n, l with
    | O, x::_    => Some x
    | S p, _::xs => nth_option A p xs
    | _, nil     => None
  end.
Implicit Arguments nth_option [A].

Fixpoint nth_option' (A : Set) (n : nat) (l : list A) {struct n} : option A :=
  match n, l with
    | O, x::_    => Some x
    | S p, _::xs => nth_option' A p xs
    | _, nil     => None
  end.
Implicit Arguments nth_option' [A]. *)

Implicit Arguments nth_option [A].
Implicit Arguments nth_option' [A].

Theorem diff_principle_arg_same_result :
  forall (A : Set) (n : nat) (l : list A), nth_option n l = nth_option' n l.
Proof.
  simple induction n.

    intros l.
    case l.
      simpl. reflexivity.
      simpl. trivial.

    intros n'.
    intros h1 l.
    simpl. case l.

      simpl. reflexivity.

      intros a l'.
      simpl.
      apply (h1 l').
Qed.

(* Exercise 6.40 On (too) short lists. *)

(* Fixpoint nth_option (A : Set) (n : nat) (l : list A) {struct l} : option A :=
  match n, l with
    | O, x::_    => Some x
    | S p, _::xs => nth_option A p xs
    | _, nil     => None
  end.
Implicit Arguments nth_option [A]. *)

Theorem nth_length :
  forall (A : Set) (n : nat) (l : list A), nth_option n l = None <-> length l <= n.
Proof.
  simple induction n.
    destruct l.
      simpl. split.
        trivial.
        trivial.
      simpl. split.
        inversion 1.
        inversion 1.
    intros n' h1 l.
    destruct l.
      simpl. split.
        auto with arith.
        trivial.
      simpl (length (a::l)).
      simpl (nth_option (S n') (a::l)).
      split.
        (* The key is that import both
          "nth_option n l = None <-> length l <= n"
          and "nth_option n l = None <-> length l <= n" into hypotheses. *)
        case (h1 l). auto with arith.
        case (h1 l). auto with arith.
Qed.

(* Exercise 6.41 Finding the first element satisfying a boolean predicate in a list. *)

Fixpoint first_satisfy_f (A : Set) (f : A -> bool) (l : list A) {struct l} : option A :=
  match l with
    | nil => None
    | x::xs => if f x then Some x else first_satisfy_f A f xs
  end.
Implicit Arguments first_satisfy_f [A].

(* Exercise 6.42 Splitting and combining lists. *)

Fixpoint split (A B : Set) (l : list (A * B)) {struct l} : list A * list B :=
  match l with
    | nil          => (nil, nil)
    | (a, b) :: xs =>
      let (la, lb) := split A B xs
      in (a::la, b::lb)
  end.
Implicit Arguments split [A B].

Fixpoint combine (A B : Set) (la : list A) (lb : list B) {struct la} : list (A * B) :=
  match la, lb with
    | a::ax, b::bx => (a, b) :: combine A B ax bx
    | _, _         => nil
  end.
Implicit Arguments combine [A B].

Theorem combine_of_split :
  forall (A B : Set) (l : list (A * B)),
    let (la, lb) := split l
    in combine la lb = l.
Proof.
  simple induction l.

    simpl; reflexivity.

    intros a l'.
    simpl (split (a::l')).
    case (split l'). (* Important step !! *)
    case a. simpl.
    destruct 1. reflexivity.
Qed.

(* Exercise 6.43 Monomorphic binary trees and polymorphic trees. *)

Inductive Z_binary_tree : Set :=
  | Zbleaf : Z_binary_tree
  | Zbnode : Z -> Z_binary_tree -> Z_binary_tree -> Z_binary_tree.

Inductive binary_tree (A : Set) : Set :=
  | bleaf : binary_tree A
  | bnode : A -> binary_tree A -> binary_tree A -> binary_tree A.

Fixpoint Z_to_normal (t : Z_binary_tree) {struct t} : binary_tree Z :=
  match t with
    | Zbleaf       => bleaf Z
    | Zbnode v l r => bnode Z v (Z_to_normal l) (Z_to_normal r)
  end.

Fixpoint normal_to_Z (t : binary_tree Z) {struct t} : Z_binary_tree :=
  match t with
    | bleaf _       => Zbleaf
    | bnode _ v l r => Zbnode v (normal_to_Z l) (normal_to_Z r)
  end.

Theorem normal_Z_inv :
  forall t, Z_to_normal (normal_to_Z t) = t.
Proof.
  induction t.
    simpl. reflexivity.
    simpl. rewrite IHt1; rewrite IHt2. reflexivity.
Qed.

Theorem Z_normal_inv :
  forall t, normal_to_Z (Z_to_normal t) = t.
Proof.
  induction t.
    simpl. reflexivity.
    simpl. rewrite IHt1; rewrite IHt2. reflexivity.
Qed.

(* Exercise 6.44 *)

(* Inductive RationalF : Set :=
  | vI : RationalF               (* 1 *)
  | vN : RationalF -> RationalF  (* n(x) = 1+x *)
  | vD : RationalF -> RationalF. (* d(x) = \frac{1}{1+\frac{1}{x}} *) *)

Fixpoint rational (rf : RationalF) : nat * nat :=
  match rf with
    | vI     => (1, 1)
    | vN rf' => let (a, b) := rational rf' in (a+b, b)
    | vD rf' => let (a, b) := rational rf' in (a, a+b)
  end.

(* Exercise 6.45 Computing prime numbers. *)

Inductive cmp : Set :=
  | Less
  | Equal
  | Greater.

(* Compare two natural number. *)
Fixpoint three_way_compare (n m : nat) {struct n} : cmp :=
  match n, m with
    | O, O     => Equal
    | O, S _   => Less
    | S _, O   => Greater
    | S a, S b => three_way_compare a b
  end.

(* For given "k" and "[(p, m)]", "m_i" is the smallest multiple of "p_i" greater
  than or equal to "k", return "[(p, m')]" where "m'_i" is the smallest multiple
  of "p_i" strictly greater than "k", and "b", a boolean value that is "true" if
  one of the "m" was equal to "k". *)
Fixpoint update_primes (k : nat) (l : list (nat * nat)) {struct l} : list (nat * nat) * bool :=
  match l with
    | nil => (nil, false)
    | (p, m) :: xs =>
      let
        (l', b) := update_primes k xs
      in
        match three_way_compare k m with
          | Less    => ((p, m) :: l', b)
          | Equal   => ((p, m+p) :: l', true)
          | Greater => ((p, m+p) :: l', b)
        end
  end.

(* For given "k", return "[(p, m)]" where "p_i" is a prime number smaller than or
  equal to "k" and "m_i" is the smallest multiple of "p" greater than or equal to
  "k+1" (strictly greater than "k"). *)
Fixpoint prime_sieve (k : nat) {struct k} : list (nat * nat) :=
  match k with
    | O => nil
    | 1 => nil
    | S k' =>
      let (l', b) := update_primes k (prime_sieve k')
      in if b
        then l'
        else (k, 2*k)::l'
  end.

(* TODO prove that "prime_sieve" can compute all prime numbers smaller than "k". *)

(* Exercise 6.46 Manual injection on variably dependent types. *)

(* Inductive htree (A : Set) : nat -> Set :=
  | hleaf : A -> htree A O
  | hnode :
    forall n : nat, A -> htree A n -> htree A n -> htree A (S n). *)

Theorem htree_injection :
  forall (n : nat) (t1 t2 t3 t4 : htree nat n), hnode nat n O t1 t2 = hnode nat n O t3 t4 -> t1 = t3.
Proof.
  intros n t1 t2 t3 t4 h1.
  injection h1.
  (* TODO *)
Admitted.

(* Exercise 6.47 Trees with fixed height. *)

(* Inductive htree (A : Set) : nat -> Set :=
  | hleaf : A -> htree A O
  | hnode :
    forall n : nat, A -> htree A n -> htree A n -> htree A (S n). *)

Fixpoint build_htree (n : nat) {struct n} : htree Z n :=
  match n return htree Z n with
    | O => hleaf Z 0%Z
    | S n' => hnode Z n' 0%Z (build_htree n') (build_htree n')
  end.

(* Exercise 6.48 Binary words. *)

Inductive binary_word : nat -> Set :=
  | nil_word  : binary_word O
  | cons_word :
    forall n : nat, bool -> binary_word n -> binary_word (S n).

Fixpoint binary_word_concat (n m : nat) (w1 : binary_word n) (w2 : binary_word m) {struct w1} : binary_word (n + m) :=
  match w1 in binary_word n return binary_word (n+m) with
    | nil_word          => w2
    | cons_word n' x xs => cons_word (n'+m) x (binary_word_concat n' m xs w2)
  end.

(* Exercise 6.49 Bit-wise or on binary words. *)

(* TODO *)

(* Fixpoint binary_word_or (n : nat) (w1 w2 : binary_word n) {struct w1} : binary_word n :=
  match w1, w2 with
    | cons_word n' a w1', cons_word _ b w2' => cons_word n' (orb a b) (binary_word_or n' w1' w2')
    | _, _ => nil_word
  end. *)

(* Exercise 6.50 A function returning a value in a dependent type. *)

(* TODO *)

(* Exercise 6.51 On the empty set. *)

Theorem empty_all_equal :
  forall a b : Empty_set, a = b.
Proof.
  intros a b.
  induction a.
Qed.

Theorem empty_all_diff :
  forall a b : Empty_set, a <> b.
Proof.
  intros a b.
  induction a.
Qed.

End Exercises.

End InductiveDataTypes.
