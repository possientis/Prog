Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.


(* The continuum hypothesis says that the continuum is the first uncountable.   *)
Definition CH : Prop := card :P(:N) = Aleph!:1:.

(* The generalized continuum hypothesis says every Aleph powers to the next one.*)
Definition GCH : Prop := forall a, Ordinal a ->
  card :P(Aleph!a) = Aleph!(succ a).

(* The generalized continuum hypothesis implies the continuum hypothesis.       *)
Proposition WhenGCH : GCH -> CH.
Proof.
  intros H1. unfold CH.
  assert (card :P(Aleph!:0:) = Aleph!(succ :0:)) as H2. {
    apply H1, Ordinal.Zero. }
  rewrite <- Aleph.WhenZero. assumption.
Qed.
