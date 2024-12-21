Require Import ZF.Binary.Range.
Require Import ZF.Class.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Include.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The range of a class is the range of its binary class.                       *)
Definition range (P:Class) : Class := Range.range (toBinary P).

(* Quick unfolding.                                                             *)
Proposition RangeCharac : forall (P:Class) (y:U),
  range P y <-> exists x, P :(x,y):.
Proof.
  intros P y. split; intros H1.
  - apply H1.
  - apply H1.
Qed.

Proposition RangeMonotone : forall (P Q:Class),
  P :<=: Q -> range P :<=: range Q.
Proof.
  intros P Q H1 y H2. apply (proj1 (RangeCharac P y)) in H2. destruct H2 as [x H2].
  apply RangeCharac. exists x. apply H1, H2.
Qed.


