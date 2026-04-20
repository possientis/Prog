Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.Fun.From.

Definition id (a:U) : U := from a (fun x => x).

Proposition Charac : forall (a x:U),
  x :< id a <-> exists y, x = :(y,y): /\ y :< a.
Proof.
  apply From.Charac.
Qed.

Proposition Charac2 : forall (a x y:U),
  :(x,y): :< id a <-> x :< a /\ y = x.
Proof.
  apply From.Charac2.
Qed.

Proposition Satisfies : forall (a x:U),
  x :< a -> :(x,x): :< id a.
Proof.
  apply From.Satisfies.
Qed.

Proposition DomainOf : forall (a:U),
  domain (id a) = a.
Proof.
  apply From.DomainOf.
Qed.

Proposition IsRelation : forall (a:U), Relation (id a).
Proof.
  apply From.IsRelation.
Qed.

Proposition IsFunctional : forall (a:U), Functional (id a).
Proof.
  apply From.IsFunctional.
Qed.

Proposition IsFunction : forall (a:U), Function (id a).
Proof.
  apply From.IsFunction.
Qed.

Proposition IsFunctionOn : forall (a:U), FunctionOn (id a) a.
Proof.
  apply From.IsFunctionOn.
Qed.

Proposition RangeOf : forall (a:U), range (id a) = a.
Proof.
  intros a. apply Incl.DoubleInclusion. split; intros y H1.
  - apply Range.Charac in H1. destruct H1 as [x H1].
    apply Charac2 in H1. destruct H1 as [H1 H2]. subst. assumption.
  - apply Range.Charac. exists y. apply Charac2. split. 1: assumption.
    reflexivity.
Qed.

Proposition IsFun : forall (a:U), Fun (id a) a a.
Proof.
  intros a. split.
  - apply IsFunctionOn.
  - rewrite RangeOf. apply Incl.Refl.
Qed.

Proposition IsOnto : forall (a:U), Onto (id a) a a.
Proof.
  intros a. split.
  - apply IsFunctionOn.
  - apply RangeOf.
Qed.

Proposition IsOneToOne : forall (a:U), OneToOne (id a).
Proof.
  intros a. split. 1: apply IsFunctional.
  intros y x1 x2 H1 H2.
  apply Converse.Charac2, Charac2 in H1. destruct H1 as [H1 H3].
  apply Converse.Charac2, Charac2 in H2. destruct H2 as [H2 H4].
  subst. reflexivity.
Qed.

Proposition IsBijection : forall (a:U), Bijection (id a).
Proof.
  intros a. split.
  - apply IsRelation.
  - apply IsOneToOne.
Qed.

Proposition IsBijectionOn : forall (a:U), BijectionOn (id a) a.
Proof.
  intros a. split.
  - apply IsBijection.
  - apply DomainOf.
Qed.

Proposition IsBij : forall (a:U), Bij (id a) a a.
Proof.
  intros a. split.
  - apply IsBijectionOn.
  - apply RangeOf.
Qed.

Proposition IsInj : forall (a:U), Inj (id a) a a.
Proof.
  intros a. split.
  - apply IsBijectionOn.
  - rewrite RangeOf. apply Incl.Refl.
Qed.

Proposition Eval : forall (a x:U),
  x :< a -> (id a)!x = x.
Proof.
  apply From.Eval.
Qed.
