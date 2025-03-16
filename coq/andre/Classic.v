Axiom DoubleNegation : forall (A:Prop), ~~A -> A.

Proposition AImpliesA : forall (A:Prop), A -> A.
Proof.
intros A H1. assumption.
Qed.

Proposition LEM : forall (A:Prop), A \/ ~A.
Proof.
intros A. apply DoubleNegation.
intros H1.
assert (~A) as H2. { intros H2. apply H1. left. assumption. }
assert (~~A) as H3. { intros H3. apply H1. right. assumption. }
apply H2. apply DoubleNegation. assumption.
Qed.

Proposition NotForAll : forall (A:Type)(P:A -> Prop),
  ~ (forall x, P x) <-> exists x, ~ P x.
Proof.
intros A P. split.
- intros H1. apply DoubleNegation. intros H2. apply H1. intros x.
  apply DoubleNegation. intros H3. apply H2. exists x. assumption.
- intros H1 H2. destruct H1 as [x H1]. apply H1. apply H2.
Qed.

