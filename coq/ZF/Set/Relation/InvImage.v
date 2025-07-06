Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.

Export ZF.Notation.Image.
Export ZF.Notation.Inverse.

Proposition Charac : forall (f a x:U),
  x :< f^:-1: :[a]: <-> exists y, y :< a /\ :(x,y): :< f.
Proof.
  intros f a x. split; intros H1.
  - apply Image.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Converse.Charac2 in H2. exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply Image.Charac. exists y.
    split. 1: assumption. apply Converse.Charac2Rev. assumption.
Qed.

(* The inverse image is compatible with set inclusion.                          *)
Proposition InclCompat : forall (f g a b:U),
  f :<=: g -> a :<=: b -> f^:-1: :[a]: :<=: g^:-1: :[b]:.
Proof.
  intros f g a b H1 H2. apply Image.InclCompat. 2: assumption.
  apply Converse.InclCompat. assumption.
Qed.

(* The inverse image is left-compatible with set inclusion.                     *)
Proposition InclCompatL : forall (f g a:U),
  f :<=: g -> f^:-1: :[a]: :<=: g^:-1: :[a]:.
Proof.
  intros f g a H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

(* The inverse image is right-compatible with set inclusion.                    *)
Proposition InclCompatR : forall (f a b:U),
  a :<=: b -> f^:-1: :[a]: :<=: f^:-1: :[b]:.
Proof.
  intros f a b H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition OfRange : forall (f:U),
  f^:-1::[range f]: = domain f.
Proof.
  intros f.
  assert (domain f^:-1: = range f) as H1. { apply Converse.Domain. }
  assert (range f^:-1: = domain f) as H2. { apply Converse.Range. }
  rewrite <- H1, <- H2. apply Range.ImageOfDomain.
Qed.

(* Characterisation of the inverse image f^(-1)[b] in terms of evaluations of f.*)
Proposition EvalCharac : forall (f b:U), Functional f ->
  forall x, x :< f^:-1: :[b]: <-> x :< domain f /\ f!x :< b.
Proof.
  intros f b H1 x. split; intros H2.
  - apply Charac in H2. destruct H2 as [y [H2 H3]].
    assert (x :< domain f) as H4. { apply Domain.Charac. exists y. assumption. }
    assert (f!x = y) as H5. { apply Eval.Charac; assumption. }
    split. 1: assumption. rewrite H5. assumption.
  - destruct H2 as [H2 H3]. apply Domain.Charac in H2. destruct H2 as [y H2].
    assert (x :< domain f) as H4. { apply Domain.Charac. exists y. assumption. }
    assert (f!x = y) as H5. { apply Eval.Charac; assumption. }
    apply Charac. exists y. split. 2: assumption. rewrite H5 in H3. assumption.
Qed.

Proposition OfImageIsLess : forall (f a:U),
  Functional f^:-1: -> f^:-1::[ f:[a]: ]: :<=: a.
Proof.
  intros f a H1 x H2. apply Charac in H2. destruct H2 as [y [H2 H3]].
  apply Image.Charac in H2. destruct H2 as [x' [H2 H4]].
  assert (x' = x) as H5. { apply Converse.WhenFunctional with f y; assumption. }
  subst. assumption.
Qed.

Proposition OfImageIsMore : forall (f a:U),
  a :<=: domain f -> a :<=: f^:-1::[ f:[a]: ]:.
Proof.
  intros f a H1 x H2. specialize (H1 x H2).
  apply Domain.Charac in H1. destruct H1 as [y H1].
  apply Charac. exists y. split. 2: assumption.
  apply Image.Charac. exists x. split; assumption.
Qed.

Proposition ImageIsLess : forall (f b:U),
  Functional f -> f:[ f^:-1::[b]: ]: :<=: b.
Proof.
  intros f b H1 y H2. apply Image.Charac in H2. destruct H2 as [x [H2 H3]].
  apply Charac in H2. destruct H2 as [y' [H2 H4]].
  assert (y' = y) as H5. { apply H1 with x; assumption. }
  subst. assumption.
Qed.

Proposition ImageIsMore : forall (f b:U),
  b :<=: range f -> b :<=: f:[ f^:-1::[b]: ]:.
Proof.
  intros f b H1 y H2. specialize (H1 y H2).
  apply Range.Charac in H1. destruct H1 as [x H1].
  apply Image.Charac. exists x. split. 2: assumption.
  apply Charac. exists y. split; assumption.
Qed.
