Require Import Relations.
Require Import Setoids.Setoid.

Inductive rel1 {A:Type} : A -> A -> Prop :=
  | rel1_refl : forall x:A, rel1 x x.

Inductive rel2 {A:Type} : A -> A -> Prop :=
  | rel2_refl : forall x:A, rel2 x x.

Lemma L1: forall (A:Type) (x y:A),
  rel1 x y <-> rel2 x y.
Proof. 
  intros A x y. split. 
    intro H. generalize H. elim H.
      clear H x y. intros. apply rel2_refl.
    intro H. generalize H. elim H.
      clear H x y. intros. apply rel1_refl.
Qed.

Lemma L2: forall (A:Type), same_relation A rel1 rel2.
Proof.
  intro A. unfold same_relation. split.
    unfold inclusion. intros x y H. rewrite <- L1. exact H.
    unfold inclusion. intros x y H. rewrite    L1. exact H.
Qed.


Lemma application1: forall (A:Type) (x y:A),
  rel1 x y -> rel2 x y.
Proof.
  intros A x y H. apply L2 in H. exact H.
Qed.
  
Lemma application2: forall (A:Type) (x y :A) (p:Prop),
  p/\rel1 x y -> p/\rel2 x y.
Proof.
  intros A x y p H. rewrite <- L1. exact H.




    
