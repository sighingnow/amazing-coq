(* Solution for exercieses in Tsinghua Coq Summber School.
  Exercise for leture 2: Datatypes, pattern-matching, and recursion by Yves Bertot. *)
Section Exercise_2_Work.

Require Import List.
Require Import ZArith.

(* Define a datatype of binary trees where non-atomic nodes have only two
  components which are binary trees, and only atomic nodes carry an integer
  value.  Include a case for empty trees. *)

Inductive PolymorphicBalancedTree (A : Type) : Type :=
  | Empty
  | Atomic (value : A)
  | Branch (l : PolymorphicBalancedTree A) (r : PolymorphicBalancedTree A).

Implicit Arguments Empty [A].
Implicit Arguments Atomic [A].
Implicit Arguments Branch [A].

(* Option type as a polymorphic datatype. *)
Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Inductive ZBalancedTree : Type :=
  | ZEmpty
  | ZAtomic (value : Z)
  | ZBranch (l : ZBalancedTree) (r : ZBalancedTree).

(* Define a function that takes a list as input and constructs a balanced
  binary tree carrying the same values.  The trick is to interchange the
  the two components of each node after inserting an integer into the first
  node. *)

Inductive NatBalancedTree : Type :=
  | NatEmpty
  | NatAtomic (value : nat)
  | NatBranch (l : NatBalancedTree) (r : NatBalancedTree).

Fixpoint nat_ge_bool_local (n m : nat): bool :=
  match n, m with
    | _, O     => true
    | O, S _   => false
    | S a, S b => nat_ge_bool_local a b
  end.

Fixpoint nat_le_bool_local (n m : nat) : bool :=
  match n, m with
    | O, _     => true
    | S _, O   => false
    | S a, S b => nat_le_bool_local a b
  end.

Fixpoint maximum_val (t : NatBalancedTree) : nat :=
  match t with
    | NatEmpty      => O
    | NatAtomic v   => v
    | NatBranch l r =>
      if (nat_ge_bool_local (maximum_val l) (maximum_val r))
        then maximum_val l
        else maximum_val r
  end.

Fixpoint insert_element (x : nat) (t : NatBalancedTree) : NatBalancedTree :=
  match t with
    | NatEmpty      => NatAtomic x
    | NatAtomic val => NatBranch (NatAtomic x) (NatAtomic val)
    | NatBranch l r =>
      if (nat_le_bool_local x (maximum_val l))
        then NatBranch (insert_element x l) r
        else NatBranch l (insert_element x r)
  end.

Fixpoint construct_tree (xs : list nat) : NatBalancedTree :=
  match xs with
    | nil         => NatEmpty
    | cons x rest => insert_element x (construct_tree rest)
  end.

(* Define a function with three arguments: a natural number and two
  lists, which builds a new list by always taking the least element
  of the heads of the two lists.  The length of the resulting list should
  be the natural number given as first input (if the two lists are long enough).

  This is a merge function as in the "merge sort" algorithm, except that the
  natural number argument should be the sum of the lengths of the two input
  lists.
*)

Fixpoint merge_nat_list_n (n : nat) (us : list nat) (vs : list nat) : list nat :=
  match n with
    | O   => nil
    | S p =>
      match us, vs with
        | cons a uss, cons b vss =>
          if (nat_le_bool_local a b)
            then a :: merge_nat_list_n p uss vs
            else b :: merge_nat_list_n p us vss
        | cons _ _, nil          => us
        | nil, cons _ _          => vs
        | nil, nil               => nil
      end
    end.

(* Define a function that merges two lists bu first computing the sum of their
  lengths and then calling the previous function. *)

Definition merge_nat_list (us vs : list nat) : list nat :=
  merge_nat_list_n (length us + length vs) us vs.

(* Eval compute in merge_nat_list (1::3::5::7::9::nil) (2::4::6::8::10::nil). *)

(* Define a recursive function on binary trees which returns a sorted list:
  - on empty trees it returns the empty list
  - on leaf treeas carrying one value, it returns a singleton list
  - on binary nodes, it returns the merge of the two sorted lists obtained
    from the sub-components. *)

Fixpoint destruct_tree (t : NatBalancedTree) : list nat :=
  match t with
    | NatEmpty      => nil
    | NatAtomic v   => v::nil
    | NatBranch l r => merge_nat_list (destruct_tree l) (destruct_tree r)
  end.

(* Eval compute in destruct_tree (construct_tree (1::3::5::7::9::2::4::6::8::10::nil)). *)

(* Define a function that sorts a list by first constructing a balanced binary
  tree and then by calling the function above. *)

Fixpoint sort_via_tree (xs : list nat) : list nat :=
  destruct_tree (construct_tree xs).

(* Eval compute in sort_via_tree (1::3::5::7::9::2::4::6::8::10::nil). *)

End Exercise_2_Work.
