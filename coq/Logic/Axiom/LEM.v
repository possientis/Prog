Require Import Logic.Axiom.Wec.

Definition LEM : Prop := forall (A:Prop), Wec A.

Lemma LEMpWec : LEM -> forall (a:Type) (p:a -> Prop), pWec p.
Proof.
    intros L a p x. apply L.
Qed.

Lemma LEMpWec2 : LEM -> forall (a b:Type) (p:a -> b -> Prop), pWec2 p.
Proof.
    intros L a b p x y. apply L.
Qed.

Lemma LEMOr : LEM -> forall (p q:Prop), (~p -> q) <-> p \/ q.
Proof.
    unfold LEM. intros L p q. split; intros H.
    - destruct (L p) as [H'|H'].
        + left. assumption.
        + right. apply H. assumption.
    - intros H1. destruct H as [H2|H2].
        + exfalso. apply H1. assumption.
        + assumption.
Qed.

Lemma LEMAnd : LEM -> forall (p q:Prop), ~(~~p -> ~q) <-> p /\ q.
Proof.
    unfold LEM. intros L p q. split.
    - intros H. split.
        + destruct (L p) as [H'|H'].
            * assumption.
            * exfalso. apply H. intros H''. exfalso.
              apply H''. assumption.
        + destruct (L q) as [H'|H'].
            * assumption.
            * exfalso. apply H. intros. assumption.
    - intros [Hp Hq] H. apply H.
        + intros P. apply P. assumption.
        + assumption.
Qed.   

Lemma LEMExist : LEM -> forall (a:Type) (p:a -> Prop), 
    ~(forall (x:a), ~p x) <-> exists (x:a), p x.
Proof.
    unfold LEM. intros L a p. split.
    - intros H. destruct (L (exists x, p x)) as [H'|H'].
        + assumption.
        + exfalso. apply H. intros x H''. apply H'. exists x. assumption.
    - intros [x H] H'. apply (H' x). assumption.
Qed.
