Require Import ZArith List.
Open Scope Z_scope.


(* Define a datatype of binary trees where non-atomic nodes have only two
  components which are binary trees, and only atomic nodes carry an integer
  value.  Include a case for empty trees. *)

(* Define a function that takes a list as input and constructs a balanced
  binary tree carrying the same values.  The trick is to interchange the
  the two components of each node after inserting an integer into the first
  node. *)

(* Define a function with three arguments: a natural number and two
  lists, which builds a new list by always taking the least element
  of the heads of the two lists.  The length of the resulting list should
  be the natural number given as first input (if the two lists are long enough).

  This is a merge function as in the "merge sort" algorithm, except that the
  natural number argument should be the sum of the lengths of the two input
  lists.
*)

(* Define a function that merges two lists bu first computing the sum of their
  lengths and then calling the previous function. *)

(* Define a recursive function on binary trees which returns a sorted list:
  - on empty trees it returns the empty list
  - on leaf treeas carrying one value, it returns a singleton list
  - on binary nodes, it returns the merge of the two sorted lists obtained
    from the sub-components. *)

(* Define a function that sorts a list by first constructing a balanced binary
  tree and then by calling the function above. *)
