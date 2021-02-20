Require Import Logic.Axiom.Dec.

Definition red (a b:Type) (p:a -> Prop) (q:b -> Prop) (f:a -> b) : Prop :=
   forall (x:a), p x <-> q (f x). 

Arguments red {a} {b}.

Lemma redDec : forall (a b:Type) (p:a -> Prop) (q:b -> Prop) (f:a -> b),
    red p q f -> pDec q -> pDec p.
Proof.
    intros a b p q f H1 H2 x. unfold pDec in H2. 
    unfold red in H1. specialize H1 with x. destruct H1 as [H1 H3].
    specialize H2 with (f x). destruct H2 as [H2|H2].
    - left. auto.
    - right. intros H4. apply H2, H1. assumption.
Qed.


