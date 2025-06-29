Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.
Export ZF.Notation.Image.
Export ZF.Notation.Inverse.

(* Inverse image of P by F is the direct image of P by F^(-1).                  *)
Proposition Charac : forall (F P:Class) (x:U),
  F^:-1: :[P]: x <-> exists y, P y /\ F :(x,y):.
Proof.
  intros F P x. split; intros H1.
  - destruct H1 as [y [H1 H2]]. apply Converse.Charac2 in H2.
    exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. exists y. split. 1: assumption.
    apply Converse.Charac2Rev. assumption.
Qed.

(* The inverse image is compatible with equivalences.                           *)
Proposition EquivCompat : forall (F G P Q:Class),
  F :~: G -> P :~: Q -> F^:-1: :[P]: :~: G^:-1: :[Q]:.
Proof.
  intros F G P Q H1 H2. apply Image.EquivCompat. 2: assumption.
  apply Converse.EquivCompat. assumption.
Qed.

(* The inverse image is left-compatible with equivalences.                      *)
Proposition EquivCompatL : forall (F G P:Class),
  F :~: G -> F^:-1: :[P]: :~: G^:-1: :[P]:.
Proof.
  intros F G P H1. apply EquivCompat.
  - assumption.
  - apply EquivRefl.
Qed.

(* The inverse image is right-compatible with equivalences.                     *)
Proposition EquivCompatR : forall (F P Q:Class),
  P :~: Q -> F^:-1: :[P]: :~: F^:-1: :[Q]:.
Proof.
  intros F P Q H1. apply EquivCompat.
  - apply EquivRefl.
  - assumption.
Qed.

(* The inverse image is compatible with inclusion.                              *)
Proposition InclCompat : forall (F G P Q:Class),
  F :<=: G -> P :<=: Q -> F^:-1: :[P]: :<=: G^:-1: :[Q]:.
Proof.
  intros F G P Q H1 H2. apply Image.InclCompat. 2: assumption.
  apply Converse.InclCompat. assumption.
Qed.

(* The inverse image is left-compatible with inclusion.                         *)
Proposition InclCompatL : forall (F G P:Class),
  F :<=: G -> F^:-1: :[P]: :<=: G^:-1: :[P]:.
Proof.
  intros F G P H1. apply InclCompat.
  - assumption.
  - apply Class.Incl.Refl.
Qed.

(* The inverse image is right-compatible with inclusion.                        *)
Proposition InclCompatR : forall (F P Q:Class),
  P :<=: Q -> F^:-1: :[P]: :<=: F^:-1: :[Q]:.
Proof.
  intros F P Q H1. apply InclCompat.
  - apply Class.Incl.Refl.
  - assumption.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (F:Class),
  F^:-1::[range F]: :~: domain F.
Proof.
  intros F. apply EquivTran with F^:-1::[domain F^:-1:]:.
  - apply Image.EquivCompatR, EquivSym, Converse.Domain.
  - apply EquivTran with (range F^:-1:).
    + apply Range.ImageOfDomain.
    + apply Converse.Range.
Qed.

(* Characterisation of the inverse image F^(-1)[A] in terms of evaluations of F.*)
Proposition EvalCharac : forall (F B:Class), Functional F ->
  forall x, F^:-1: :[B]: x <-> domain F x /\ B F!x.
Proof.
  intros F B H1 x. split; intros H2.
  - destruct H2 as [y [H2 H3]]. apply Converse.Charac2 in H3.
    assert (domain F x) as H4. { exists y. assumption. }
    split. 1: assumption.
    assert (F!x = y) as H5. { apply EvalOfClass.Charac; assumption. }
    rewrite H5. assumption.
  - destruct H2 as [H2 H3]. exists (F!x). split. 1: assumption.
    apply Converse.Charac2Rev. apply EvalOfClass.Satisfies; assumption.
Qed.

Proposition InvImageOfImageIsLess : forall (F A:Class),
  Functional F^:-1: -> F^:-1::[ F:[A]: ]: :<=: A.
Proof.
  intros F A H1 x H2. apply Charac in H2. destruct H2 as [y [H2 H3]].
  destruct H2 as [x' [H2 H4]]. assert (x' = x) as H5. { apply H1 with y.
    - apply Converse.Charac2Rev. assumption.
    - apply Converse.Charac2Rev. assumption. }
  subst. assumption.
Qed.

Proposition InvImageOfImageIsMore : forall (F A:Class),
  A :<=: domain F -> A :<=: F^:-1::[ F:[A]: ]:.
Proof.
  intros F A H1 x H2. specialize (H1 x H2).
  destruct H1 as [y H1]. apply Charac. exists y.
  split. 2: assumption. exists x. split; assumption.
Qed.

Proposition ImageOfInvImageIsLess : forall (F B:Class),
  Functional F -> F:[ F^:-1::[B]: ]: :<=: B.
Proof.
  intros F B H1 y H2.
  destruct H2 as [x [H2 H3]].
  apply Charac in H2. destruct H2 as [y' [H2 H4]].
  assert (y' = y) as H6. { apply H1 with x; assumption. }
  subst. assumption.
Qed.

Proposition ImageOfInvImageIsMore : forall (F B:Class),
  B :<=: range F -> B :<=: F:[ F^:-1::[B]: ]:.
Proof.
  intros F B H1 y H2. specialize (H1 y H2).
  destruct H1 as [x H1]. exists x. split. 2: assumption.
  apply Charac. exists y. split; assumption.
Qed.

