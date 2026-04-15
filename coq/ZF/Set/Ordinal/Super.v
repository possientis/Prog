Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Super.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module COS := ZF.Class.Ordinal.Super.
Module SUG := ZF.Set.UnionGenOfClass.

(* Predicate defining a supertransitive set.                                    *)
Definition Super (a:U) : Prop := Transitive a /\
  forall x, x :< a -> :P(x) :<=: a.

Proposition ToClass : forall (a:U),
  Super a -> COS.Super (toClass a).
Proof.
  intros a [H1 H2]. split.
  - apply Transitive.ToClass. assumption.
  - intros x H3. apply H2. assumption.
Qed.

Proposition FromClass : forall (a:U),
  COS.Super (toClass a) -> Super a.
Proof.
  intros a [H1 H2]. split.
  - apply Transitive.FromClass. assumption.
  - intros x H3. apply H2. assumption.
Qed.

Proposition WhenZero : forall (a:U),
  a = :0: -> Super a.
Proof.
  intros a H1. split.
  - apply Transitive.WhenZero. assumption.
  - intros x H2. subst. apply Empty.Charac in H2. contradiction.
Qed.

Proposition WhenPower : forall (a:U),
  Super a -> Super :P(a).
Proof.
  intros a [H1 H2]. split.
  - apply Transitive.WhenPower. assumption.
  - intros b H3 c H4. apply Power.Charac in H3. apply Power.Charac in H4.
    apply Power.Charac. intros x H5. apply (H2 x).
    + apply H3, H4. assumption.
    + apply Power.IsIn.
Qed.

Proposition WhenUnion : forall (F:Class) (a:U),
  (forall x, x :< a -> Super F!x) -> Super (:\/:_{a} F).
Proof.
  intros F a H1. split.
  - apply Transitive.WhenUnion. intros x H2. apply H1. assumption.
  - intros y H2 x H3.
    apply SUG.Charac in H2. destruct H2 as [b [H2 H4]].
    apply SUG.Charac. exists b. split. 1: assumption. specialize (H1 b H2).
    destruct H1 as [H1 H5]. apply (H5 y); assumption.
Qed.
