Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Single.

Definition OrdFunOn (f a:U) : Prop := OrdFun f /\ domain f = a.

Proposition IsOrdinal : forall (f a x:U), OrdFunOn f a ->
  x :< a -> Ordinal f!x.
Proof.
  intros f a x H1 H2.
  apply OrdFun.IsOrdinal.
  - apply H1.
  - assert (domain f = a) as H3. { apply H1. }
    subst. assumption.
Qed.

Proposition DomainOf : forall (f a:U), OrdFunOn f a -> Ordinal a.
Proof.
  intros f a [[H1 [H2 H3]] H4]. subst. assumption.
Qed.

Proposition WhenEmpty : forall (f:U),
  f = :0: <-> OrdFunOn f :0:.
Proof.
  intros f. split; intros H1.
  - split.
    + apply OrdFun.WhenEmpty. assumption.
    + apply Domain.WhenEmpty. assumption.
  - destruct H1 as [[H1 _] H2].
    assert (f = :0: \/ f <> :0:) as H3. { apply LawExcludedMiddle. }
    destruct H3 as [H3|H3]. 1: assumption. exfalso.
    apply Empty.HasElem in H3. destruct H3 as [x H3].
    assert (exists y z, x = :(y,z):) as H4. { apply H1. assumption. }
    destruct H4 as [y [z H4]].
    assert (y :< domain f) as H5. {
      apply Domain.Charac. exists z. subst. assumption. }
    rewrite H2 in H5. apply Empty.Charac in H5. contradiction.
Qed.

Proposition WhenSingle : forall (a f:U), Ordinal a ->
  f = :{ :(:0:,a): }: -> OrdFunOn f :1:.
Proof.
  intros a f H1 H2. split.
  - apply OrdFun.WhenSingle with a; assumption.
  - rewrite Domain.WhenSingle with :0: a f. 2: assumption.
    symmetry. apply Natural.OneExtension.
Qed.

