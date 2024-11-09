Require Import Logic.ZF.Core.

(* If the proposition ~A leads to a contradiction, then A is true.              *)
Axiom DoubleNegation : forall (A:Prop), ~~A -> A.

(* If a predicate being never satisfied is false then it is satisfied by some x.*)
Proposition NotForAllNot : forall (P:U -> Prop),
  ~ (forall x, ~ P x) <-> exists x, P x.
Proof.
  intros P. split; intros H1.
  - apply DoubleNegation. intros H2. apply H1.
    intros a H3. apply H2. exists a. apply H3.
  - destruct H1 as [a H1]. intros H2. apply (H2 a), H1.
Qed.

Proposition LawExcludedMiddle : forall (A:Prop), A \/ ~A.
Proof.
  intros A. apply DoubleNegation. intros H1.
  assert (~A) as H2. { intros H3. apply H1. left. apply H3. }
  assert (~~A) as H3. { intros _. apply H1. right. apply H2. }
  contradiction.
Qed.
