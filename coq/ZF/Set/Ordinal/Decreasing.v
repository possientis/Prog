Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Single.

Definition Decreasing (f:U) : Prop := forall (x y:U),
  x   :< domain f ->
  y   :< domain f ->
  x   :< y        ->
  f!y :< f!x.

Proposition WhenSingle : forall (x y f:U),
  f = :{ :(x,y): }: -> Decreasing f.
Proof.
  intros x y f H1 u v H2 H3 H4. exfalso.
  rewrite Domain.WhenSingle with x y f in H2. 2: assumption.
  rewrite Domain.WhenSingle with x y f in H3. 2: assumption.
  apply Single.Charac in H2. apply Single.Charac in H3. subst.
  revert H4. apply NoElemLoop1.
Qed.

Proposition Relax : forall (f x y:U),
  OrdFun f        ->
  Decreasing f    ->
  x :< domain f   ->
  y :< domain f   ->
  x :<=: y        ->
  f!y :<=: f!x.
Proof.
  intros f x y H1 H2 H3 H4 H5. assert (H6 := H1). destruct H6 as [H6 [H7 H8]].
  assert (Ordinal x) as G1. {
    apply Core.IsOrdinal with (domain f); assumption. }
  assert (Ordinal y) as G2. {
    apply Core.IsOrdinal with (domain f); assumption. }
  assert (Ordinal f!x) as G3. { apply OrdFun.IsOrdinal; assumption. }
  assert (Ordinal f!y) as G4. { apply OrdFun.IsOrdinal; assumption. }
  assert (x = y \/ x :< y) as H9. { apply Core.EqualOrElem; assumption.  }
  destruct H9 as [H9|H9].
  - subst. apply Incl.Refl.
  - apply Core.ElemIsIncl. 1: assumption. apply H2; assumption.
Qed.
