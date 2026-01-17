Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Single.

(* An ordinal function is a function with ordinal domain and ordinal values.    *)
Definition OrdFun : Class := fun f =>
  Function f                              /\
  Ordinal (domain f)                      /\
  (forall y, y :< range f -> Ordinal y).

Proposition IsOrdinal : forall (f x:U), OrdFun f ->
  x :< domain f -> Ordinal f!x.
Proof.
  intros f x [H1 [H2 H3]] H4. assert (H5 := H4).
  apply Domain.Charac in H5. destruct H5 as [y H5].
  assert (f!x = y) as H6. { apply Eval.Charac; try assumption. apply H1. }
  rewrite H6. apply H3. apply Range.Charac. exists x. assumption.
Qed.

Proposition DomainOf : forall (f:U),
  OrdFun f -> Ordinal (domain f).
Proof.
  intros f [_ [H1 _]]. assumption.
Qed.

Proposition WhenEmpty : forall (f:U),
  f = :0: -> OrdFun f.
Proof.
  intros f H1. split.
  - apply Function.WhenEmpty. assumption.
  - split.
    + assert (domain f = :0:) as H2. { apply Domain.WhenEmpty. assumption. }
      rewrite H2. apply Core.ZeroIsOrdinal.
    + intros y H2.
      assert (range f = :0:) as H3. { apply Range.WhenEmpty. assumption. }
      rewrite H3 in H2. apply Empty.Charac in H2. contradiction.
Qed.

Proposition WhenSingle : forall (a f:U),
  Ordinal a           ->
  f = :{ :(:0:,a): }: ->
  OrdFun f.
Proof.
  intros a f H1 H2. split.
  - apply Function.WhenSingle with :0: a. assumption.
  - split.
    + rewrite Domain.WhenSingle with :0: a f. 2: assumption.
      rewrite <- Natural.OneExtension. apply Natural.OneIsOrdinal.
    + intros y H3. rewrite Range.WhenSingle with :0: a f in H3.
      2: assumption. apply Single.Charac in H3. subst. assumption.
Qed.
