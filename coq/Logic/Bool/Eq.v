Require Import Logic.Class.Eq.

(* TODO: This is probably somewhere in Coq library                              *)
Definition bool_eq_dec : forall (a b:bool), {a = b} + {a <> b}.
Proof.
    intros a b. destruct a eqn:E1; destruct b eqn:E2.
    - left. reflexivity.
    - right. intros H1. inversion H1.
    - right. intros H1. inversion H1.
    - left. reflexivity.
Defined.

Instance EqBool : Eq bool := { eqDec := bool_eq_dec }.

Lemma onlyTwoElements : forall (a b c:bool),
    a <> b -> a <> c -> b <> c -> False.
Proof.
    intros a b c H1 H2 H3. destruct a, b, c; try auto.
Qed.


