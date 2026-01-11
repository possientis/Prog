Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.ShiftL.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.

Module COS := ZF.Class.Ordinal.ShiftL.

(* Shifting a function to the left. shiftL f = { (x,y) | (succ x, y) :< f }     *)
Definition shiftL (f:U) : U := fromClass (COS.shiftL (toClass f))
  (COS.IsSmall (toClass f) (SetIsSmall f)).

Proposition ToClass : forall (f:U),
  toClass (shiftL f) :~: COS.shiftL (toClass f).
Proof.
  intros f. apply ToFromClass.
Qed.

Proposition Charac : forall (f x:U),
  x :< shiftL f <-> exists y z, x = :(y,z): /\ :(succ y, z): :< f.
Proof.
  intros f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y [z [H1 H2]]]. subst.
    exists y, z. split. 2: assumption. reflexivity.
  - destruct H1 as [y [z [H1 H2]]]. apply FromClass.Charac.
    exists y, z. split; assumption.
Qed.

Proposition Charac2 : forall (f y z:U),
  :(y,z): :< shiftL f <-> :(succ y, z): :< f.
Proof.
  intros f y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [u [v [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. assumption.
  - apply Charac. exists y, z. split. 2: assumption. reflexivity.
Qed.

Proposition IsRelation : forall (f:U), Relation (shiftL f).
Proof.
  intros f x H1. apply Charac in H1. destruct H1 as [y [z [H1 _]]]. subst.
  exists y, z. reflexivity.
Qed.

Proposition IsFunctional : forall (f:U),
  Functional f -> Functional (shiftL f).
Proof.
  intros f H1 x y1 y2 H2 H3.
  apply Charac2 in H2. apply Charac2 in H3.
  apply H1 with (succ x); assumption.
Qed.

Proposition IsFunction : forall (f:U),
  Functional f -> Function (shiftL f).
Proof.
  intros f H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Proposition DomainOf : forall (f x:U),
  x :< domain (shiftL f) <-> succ x :< domain f.
Proof.
  intros f x. split; intros H1;
  apply Domain.Charac in H1; destruct H1 as [y H1].
  - apply Charac2 in H1. apply Domain.Charac. exists y. assumption.
  - apply Domain.Charac. exists y. apply Charac2. assumption.
Qed.

Proposition Eval : forall (f x:U), Functional f ->
  succ x :< domain f -> (shiftL f)!x = f!(succ x).
Proof.
  intros f x H1 H2. apply Eval.Charac.
  - apply IsFunctional. assumption.
  - apply DomainOf. assumption.
  - apply Charac2. apply Eval.Satisfies; assumption.
Qed.

Proposition RangeOf : forall (f:U),
  range (shiftL f) :<=: range f.
Proof.
  intros f y H1. apply Range.Charac in H1. destruct H1 as [x H1].
  apply Charac2 in H1. apply Range.Charac. exists (succ x). assumption.
Qed.

Proposition WhenOrdinalDomain : forall (f:U), Ordinal (domain f) ->
  domain (shiftL f) = :U(domain f).
Proof.
  intros f H1. apply DoubleInclusion. split; intros x H2.
  - apply DomainOf in H2. apply Union.Charac. exists (succ x).
    split. 2: assumption. apply Succ.IsIn.
  - apply Union.Charac in H2. destruct H2 as [y [H2 H3]]. apply DomainOf.
    assert (Ordinal y) as H4. { apply Core.IsOrdinal with (domain f); assumption. }
    assert (Ordinal x) as H5. { apply Core.IsOrdinal with y; assumption. }
    assert (Ordinal (succ x)) as H6. { apply Succ.IsOrdinal. assumption. }
    assert (succ x :<=: y) as H7. { apply Succ.ElemIsIncl; assumption. }
    assert (succ x = y \/ succ x :< y) as H8. {
      apply Core.EqualOrElem; assumption. }
    destruct H8 as [H8|H8].
    + subst. assumption.
    + apply Core.ElemElemTran with y; assumption.
Qed.
