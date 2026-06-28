Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Rank.VH.
Require Import ZF.Class.Empty.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGen.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Rank.Core.
Require Import ZF.Set.Rank.MinRank.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module SRC := ZF.Set.Rank.Core.
Module SOG := ZF.Set.Ordinal.UnionGen.
Module SUG := ZF.Set.UnionGen.


Proposition HasBound : forall (A:Class) (a:U),
  (forall x, x :< a -> exists y, A :(x,y):) -> exists b,
  (forall x, x :< a -> exists y, A :(x,y): /\ y :< b).
Proof.
  intros A a H1.
  remember (fun x y => A :(x,y):) as B eqn:H2.
  remember (fun x => minRank (B x)) as C eqn:H3.
  remember (From.from a C) as g eqn:H4.
  assert (FunctionOn g a) as H5. { rewrite H4. apply From.IsFunctionOn. }
  assert (forall x, x :< a -> Ordinal g!x) as H6. {
    intros x H6. rewrite H4, From.Eval, H3. 2: assumption.
    apply MinRank.IsOrdinal. }
  remember (:\/:_{a} g) as c eqn:H7.
  assert (Ordinal c) as H8. {
    rewrite H7. apply SOG.IsOrdinal. assumption. }
  assert (Ordinal (succ c)) as G1. { apply Succ.IsOrdinal. assumption. }
  remember (VH!(succ c)) as b eqn:H9.
  exists b. intros x H10. specialize (H1 x H10).
  assert (exists y, A :(x,y): /\ g!x = rank y) as H11. {
    rewrite H4, From.Eval, H3, H2. 2: assumption.
    apply MinRank.IsAttained, CEM.HasElem. assumption. }
  destruct H11 as [y [H11 H12]]. exists y. split. 1: assumption.
  rewrite H9. apply SRC.IsIn. 1: assumption. rewrite <- H12, H7.
  apply Succ.InclIsElem.
  - apply H6. assumption.
  - rewrite <- H7. assumption.
  - apply SUG.IsIncl. assumption.
Qed.

Proposition Choice : forall (A:Class) (a:U), Choice ->
  (forall x, x :< a -> exists y, A :(x,y):)  ->
  exists f, FunctionOn f a                   /\
  forall x, x :< a -> A :(x,f!x):.
Proof.
Admitted.

