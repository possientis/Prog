Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module COT := ZF.Class.Ordinal.Transitive.
Module SUG := ZF.Set.UnionGenOfClass.

Definition Transitive (a:U) : Prop := forall (x y:U),
  x :< y -> y :< a -> x :< a.

Proposition ToClass : forall (a:U),
  Transitive a <-> COT.Transitive (toClass a).
Proof.
  intros a. split; intros H1.
  - intros y H2 x H3. apply H1 with y; assumption.
  - intros x y H2 H3. apply H1 with y; assumption.
Qed.

Proposition WhenOrdinal : forall (a:U), Ordinal a -> Transitive a.
Proof.
  intros a H1 x y H2 H3.
  assert (Ordinal y) as H4. { apply Core.IsOrdinal with a; assumption. }
  assert (Ordinal x) as H5. { apply Core.IsOrdinal with y; assumption. }
  apply Core.ElemElemTran with y; assumption.
Qed.

Proposition WhenZero : forall (a:U),
  a = :0: -> Transitive a.
Proof.
  intros a H1 x y H2 H3. subst. apply Empty.Charac in H3. contradiction.
Qed.

Proposition WhenPower : forall (a:U),
  Transitive a -> Transitive :P(a).
Proof.
  intros a H1 x y H2 H3.
  apply Power.Charac in H3. apply Power.Charac.
  intros u H4. apply H1 with x. 1: assumption. apply H3. assumption.
Qed.

Proposition WhenUnion : forall (F:Class) (a:U),
  (forall x, x :< a -> Transitive F!x) -> Transitive (:\/:_{a} F).
Proof.
  intros F a H1 x y H2 H3.
  apply SUG.Charac in H3. destruct H3 as [b [H3 H4]].
  apply SUG.Charac. exists b. split. 1: assumption.
  apply H1 with y; assumption.
Qed.
