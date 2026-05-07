Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module COT := ZF.Class.Ordinal.Transitive.
Module SUG := ZF.Set.UnionGenOfClass.

Definition Transitive (a:U) : Prop := forall (x y:U),
  x :< y -> y :< a -> x :< a.

(* If the set is transitive, so is the class.                                   *)
Proposition ToClass : forall (a:U),
  Transitive a -> COT.Transitive (toClass a).
Proof.
  intros a H1 y H2 x H3. apply H1 with y; assumption.
Qed.

(* If the class is transitive, so is the set.                                   *)
Proposition FromClass : forall (a:U),
  COT.Transitive (toClass a) -> Transitive a.
Proof.
  intros a H1 x y H2 H3. apply H1 with y; assumption.
Qed.

(* The empty set is transitive.                                                 *)
Proposition WhenZero : forall (a:U),
  a = :0: -> Transitive a.
Proof.
  intros a H1 x y H2 H3. subst. apply Empty.Charac in H3. contradiction.
Qed.

(* The powerset of a transitive set is transitive.                              *)
Proposition WhenPower : forall (a:U),
  Transitive a -> Transitive :P(a).
Proof.
  intros a H1 x y H2 H3.
  apply Power.Charac in H3. apply Power.Charac.
  intros u H4. apply H1 with x. 1: assumption. apply H3. assumption.
Qed.

(* The union of a family of transitive sets is transitive.                      *)
Proposition WhenUnion : forall (F:Class) (a:U),
  (forall x, x :< a -> Transitive F!x) -> Transitive (:\/:_{a} F).
Proof.
  intros F a H1 x y H2 H3.
  apply SUG.Charac in H3. destruct H3 as [b [H3 H4]].
  apply SUG.Charac. exists b. split. 1: assumption.
  apply H1 with y; assumption.
Qed.
