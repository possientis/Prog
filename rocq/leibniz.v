Section leibniz.
Set Implicit Arguments.
Unset Strict Implicit. (* ?? *)
Variable A:Set.


Definition leibniz (a b:A) : Prop :=
  forall P:A->Prop, P a -> P b.

Require Import Relations.

Theorem leibniz_sym: symmetric A leibniz.
Proof.
  unfold symmetric.
  unfold leibniz.
  intros x y H Q.
  apply H. trivial.
Qed.

Theorem leibniz_refl: reflexive A leibniz.
Proof.
  unfold reflexive. intro x. unfold leibniz. intro P. trivial.
Qed.


Theorem leibniz_trans: transitive A leibniz.
Proof.
  unfold transitive.
  intros x y z H0 H1.
  unfold leibniz.
  intros P H. apply H1. apply H0. exact H.
Qed.

Theorem leibniz_least_reflexive : 
  forall R:relation A, reflexive A R -> inclusion A leibniz R.
Proof.
  intro R. intro Refl. unfold inclusion. intros x y. intro H.
  apply H. unfold reflexive in Refl. apply Refl.
Qed.

Theorem leibniz_eq : forall a b:A, leibniz a b -> a = b.
Proof. 
  intros a b H. apply H. reflexivity.
Qed.

Theorem eq_leibniz : forall a b:A, a = b -> leibniz a b.
Proof.
  intros a b H. unfold leibniz. intro P. intro Pa. rewrite <- H. exact Pa.
Qed.


Theorem leibniz_ind : 
  forall (x:A)(P:A->Prop), P x -> forall y:A, leibniz x y -> P y.
Proof.
  intros x P Px y H. apply H. exact Px.
Qed.

Unset Implicit Arguments.
End leibniz.



