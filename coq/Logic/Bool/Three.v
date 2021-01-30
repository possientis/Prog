Require Import Logic.Class.Eq.

Inductive Three : Type :=
| zero : Three
| one  : Three
| two  : Three
.

Definition three_eq_dec : forall (a b:Three), {a = b} + {a <> b}.
Proof.
    intros a b. destruct a eqn:E1; destruct b eqn:E2.
    - left. reflexivity.
    - right. intros H1. inversion H1.
    - right. intros H1. inversion H1.
    - right. intros H1. inversion H1.
    - left. reflexivity.
    - right. intros H1. inversion H1.
    - right. intros H1. inversion H1.
    - right. intros H1. inversion H1.
    - left. reflexivity.
Qed.

Instance EqThree : Eq Three := { eqDec := three_eq_dec }.

Lemma onlyThreeElements : forall (a b c d:Three),
    a <> b -> a <> c -> a <> d -> b <> c -> b <> d -> c <> d -> False.
Proof.
    intros a b c d H1 H2 H3 H4 H5 H6. destruct a, b, c, d; try auto.
Qed.
