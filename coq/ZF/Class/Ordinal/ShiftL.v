Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Ordinal.Union.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.

Module CIN := ZF.Class.Incl.
Module COC := ZF.Class.Ordinal.Core.
Module COU := ZF.Class.Ordinal.Union.
Module SOC := ZF.Set.Ordinal.Core.

(* Shifting a function class to the left.                                       *)
Definition shiftL (F:Class) : Class := fun x => exists y z,
  x = :(y,z): /\ F :(succ y,z):.

Proposition Charac2 : forall (F:Class) (y z:U),
  shiftL F :(y,z): <-> F :(succ y,z):.
Proof.
  intros F y z. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. assumption.
  - exists y, z. split. 2: assumption. reflexivity.
Qed.

Proposition IsRelation : forall (F:Class), Relation (shiftL F).
Proof.
  intros F x H1. destruct H1 as [y [z [H1 _]]]. exists y, z. assumption.
Qed.

Proposition IsFunctional : forall (F:Class),
  Functional F -> Functional (shiftL F).
Proof.
  intros F H1 y z1 z2 H2 H3.
  apply Charac2 in H2. apply Charac2 in H3. apply H1 with (succ y); assumption.
Qed.

Proposition IsFunction : forall (F:Class),
  Functional F  -> Function (shiftL F).
Proof.
  intros F H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Proposition DomainOf : forall (F:Class) (x:U),
  domain (shiftL F) x <-> domain F (succ x).
Proof.
  intros F x. split; intros [y H1].
  - apply Charac2 in H1. exists y. assumption.
  - exists y. apply Charac2. assumption.
Qed.

Proposition Eval : forall (F:Class) (x:U), Functional F ->
  domain F (succ x) -> (shiftL F)!x = F!(succ x).
Proof.
  intros F x H1 H2.
  apply EvalOfClass.Charac.
  - apply IsFunctional. assumption.
  - apply DomainOf. assumption.
  - apply Charac2. apply EvalOfClass.Satisfies; assumption.
Qed.

Proposition RangeOf : forall (F:Class),
  range (shiftL F) :<=: range F.
Proof.
  intros F y H1. destruct H1 as [x H1]. apply Charac2 in H1.
  exists (succ x). assumption.
Qed.

Proposition WhenOrdinalDomain : forall (F:Class), COC.Ordinal (domain F) ->
  domain (shiftL F) :~: :U(domain F).
Proof.
  intros F H1. intros x. split; intros H2.
  - apply DomainOf in H2. exists (succ x). split. 2: assumption.
    apply Succ.IsIn.
  - destruct H2 as [y [H2 H3]]. apply DomainOf.
    assert (Ordinal y) as H4. { apply COC.IsOrdinal with (domain F); assumption. }
    assert (Ordinal x) as H5. { apply SOC.IsOrdinal with y; assumption. }
    assert (Ordinal (succ x)) as H6. { apply Succ.IsOrdinal. assumption. }
    assert (succ x :<=: y) as H7. { apply Succ.ElemIsIncl; assumption. }
    assert (succ x = y \/ succ x :< y) as H8. {
      apply SOC.InclIsEqualOrElem; assumption. }
    destruct H8 as [H8|H8].
    + subst. assumption.
    + assert (Transitive (domain F)) as H9. { apply H1. }
      apply H9 with y; assumption.
Qed.

Proposition IsOrdFun : forall (F:Class),
  OrdFun F  -> OrdFun (shiftL F).
Proof.
  intros F H1. split.
  - apply IsFunction. apply H1.
  - split.
    + apply COC.EquivCompat with :U(domain F).
      * apply Equiv.Sym, WhenOrdinalDomain, H1.
      * apply COU.IsOrdinal, COC.IsIncl, H1.
    + apply CIN.Tran with (range F).
      * apply RangeOf.
      * apply H1.
Qed.

