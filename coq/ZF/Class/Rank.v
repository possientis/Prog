Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.R1.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Rank.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.


(* A class with elements of bounded ranks is small.                             *)
Proposition IsSmall : forall (A:Class),
  (exists a, Ordinal a /\ forall x, A x -> rank x :<=: a) -> Small A.
Proof.
  intros A [a [H1 H2]].
  assert (Ordinal (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
  apply Bounded.IsSmall. exists R1!(succ a). intros x H3.
  assert (Ordinal (rank x)) as G2. { apply Rank.IsOrdinal. }
  apply Rank.IsIn. 1: assumption. apply Succ.InclIsElem; try assumption.
  apply H2. assumption.
Qed.

Proposition WhenProper : forall (A:Class) (a:U),
  Proper A                        ->
  Ordinal a                       ->
  exists x, A x /\ a :< rank x.
Proof.
  intros A a H1 H2.
  apply Classic.NotForAllNot. intros H3.
  apply H1, IsSmall. exists a. split. 1: assumption.
  intros x H4. specialize (H3 x).
  assert (Ordinal (rank x)) as G1. { apply Rank.IsOrdinal. }
  assert (a :< rank x \/ rank x :<=: a) as H5. { apply Core.ElemOrIncl; assumption. }
  destruct H5 as [H5|H5]. 2: assumption. exfalso.
  apply H3. split; assumption.
Qed.
