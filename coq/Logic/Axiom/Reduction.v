Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Sec.
Require Import Logic.Axiom.Sat.

Definition red (a b:Type) (p:a -> Prop) (q:b -> Prop) (f:a -> b) : Prop :=
   forall (x:a), p x <-> q (f x). 

Arguments red {a} {b}.

Definition ReducesTo (a b:Type) (p:a -> Prop) (q:b -> Prop) : Prop :=
    exists (f:a -> b), red p q f.

Arguments ReducesTo {a}{b}. 

Lemma redDec : forall (a b:Type) (p:a -> Prop) (q:b -> Prop) (f:a -> b),
    red p q f -> pDec q -> pDec p.
Proof.
    intros a b p q f H1 H2 x. unfold pDec in H2. 
    unfold red in H1. specialize H1 with x. destruct H1 as [H1 H3].
    specialize H2 with (f x). destruct H2 as [H2|H2].
    - left. auto.
    - right. intros H4. apply H2, H1. assumption.
Qed.

Lemma ReducesDecidable : forall (a b:Type) (p:a -> Prop) (q:b -> Prop),
    ReducesTo p q -> Decidable q -> Decidable p.
Proof.
    intros a b p q [f H1] [g H2]. exists (fun n => g (f n)). intros x.
    unfold red in H1. specialize H1 with x.
    unfold DeciderOf in H2. specialize H2 with (f x).
    destruct H1 as [H1 G1]. destruct H2 as [H2 G2]. split; intros H3.
    - apply H2, H1, H3.
    - apply G1, G2, H3.
Qed.

Lemma redSec : forall (a b:Type) (p:a -> Prop) (q:b -> Prop) (f:a -> b),
    red p q f -> pSec q -> pSec p.
Proof.
    intros a b p q f H1 H2 x. unfold pSec in H2.
    unfold red in H1. specialize H1 with x. destruct H1 as [H1 H3].
    specialize H2 with (f x). destruct H2 as [g H2].
    exists g. destruct H2 as [H2 H4]. split; intros H5.
    - apply H2, H1, H5.
    - apply H3, H4, H5.
Qed.

Lemma ReducesSemiDecidable : forall (a b:Type) (p:a -> Prop) (q:b -> Prop),
    ReducesTo p q -> SemiDecidable q -> SemiDecidable p.
Proof.
    intros a b p q [f H1] [F H2]. exists (fun x n => F (f x) n). intros x.
    unfold red in H1. specialize H1 with x.
    unfold SemiDeciderOf in H2. specialize H2 with (f x).
    destruct H1 as [H1 G1]. destruct H2 as [H2 G2]. split; intros H3.
    - apply H2, H1, H3.
    - apply G1, G2, H3.
Qed.

