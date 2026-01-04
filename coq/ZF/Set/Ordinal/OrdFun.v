Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Range.

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
