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
 Admitted.


 Lemma id_PP : (P -> P) -> P -> P.
 Proof.
 Admitted.

 Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
 Proof.
 Admitted.

 Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
 Proof.
 Admitted.

 Lemma ignore_Q : (P -> R) -> P -> Q -> R.
 Proof.
 Admitted.

 Lemma delta_imp : (P -> P -> Q) -> P -> Q.
 Proof.
 Admitted.

 Lemma delta_impR : (P -> Q) -> P -> P -> Q.
 Proof.
 Admitted.

 Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof.
 Admitted.

 Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
 Proof.
 Admitted.

End Minimal_propositioal_logic.


(** Same exercise as the previous one, with full intuitionistic propositional
   logic

   You may use the tactics intro[s], apply, assumption, destruct,
                           left, right, split and try to use tactic composition *)


Section propositional_logic.

 Variables P Q R S T : Prop.

 Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
 Proof.
 Admitted.

 Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
 Proof.
 Admitted.

 Lemma not_contrad :  ~(P /\ ~P).
 Proof.
 Admitted.

 Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
 Proof.
 Admitted.


 Lemma not_not_exm : ~ ~ (P \/ ~ P).
 Proof.
 Admitted.

 Lemma de_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
 Proof.
 Admitted.

 Lemma de_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
 Proof.
 Admitted.

 Lemma de_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
 Proof.
 Admitted.

End propositional_logic.

Section First_Order_Logic.

 Variable A : Set.
 Variables (P Q : A -> Prop)
           (R : A -> A -> Prop).


Lemma forall_imp_dist : (forall x:A, P x -> Q x) ->
                        (forall x:A, P x) ->
                        forall x: A, Q x.
Proof.
Admitted.

Lemma forall_perm : (forall x y:A, R x y) -> forall y x, R x y.
Proof.
Admitted.

Lemma forall_delta : (forall x y:A, R x y) -> forall x, R x x.
Proof.
Admitted.


Lemma exists_or_dist : (exists x: A, P x \/ Q x) <->
                       (exists x, P x) \/ (exists x , Q x).
Proof.
Admitted.

Lemma exists_imp_dist : (exists x: A, P x -> Q x) ->
                        (forall x:A, P x) ->
                        exists x:A, Q x.
Admitted.

Lemma not_empty_forall_exists : forall a:A,
                                 (forall x:A, P x) ->
                                  exists x:A, P x.
Proof.
Admitted.

Lemma not_ex_forall_not : ~(exists x:A, P x) <-> forall x:A, ~P x.
Proof.
Admitted.



Lemma singleton_forall_eq : (exists x:A, forall y:A, x = y) ->
                            forall z t : A, z = t.
Proof.
Admitted.




Section S1.
Variables  (f g : A -> A).

Hypothesis f_g_perm : forall x:A, f (g x) = g (f x).

Hypothesis g_idempotent : forall x : A, g (g x) = g x.
Hypothesis f_idempotent : forall x : A, f (f x) = f x.


Lemma L : forall z, g (f (g (f (g (f z))))) = f (g z).
Proof.
Admitted.


Lemma L':  (forall x : A, ~ x = f x) ->
           ~ (exists y : A, True).
Proof.
Admitted.


End S1.

