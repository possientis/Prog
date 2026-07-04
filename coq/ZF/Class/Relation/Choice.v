Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Rank.VH.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Cardinal.WellOrderable.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Minimal.
Require Import ZF.Set.Order.Total.
Require Import ZF.Set.Order.WellOrdering.
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
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Specify.
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
  intros A a AC H1.
  assert (exists b, forall x, x :< a -> exists y, A :(x,y): /\ y :< b) as H2. {
    apply HasBound. assumption. }
  destruct H2 as [b H2].
  assert (exists r, WellOrdering r b) as H3. {
    apply WellOrderable.HasWellOrdering, WellOrderable.WithChoice. assumption. }
  destruct H3 as [r H3].
  assert (Total r b) as G1. { apply H3. }
  remember (fun x => {{ y :< b | fun y => A :(x,y): }}) as c eqn:H4.
  remember (fun z => exists x y,
    z = :(x,y):                     /\
    A :(x,y):                       /\
    Minimal r (c x) y) as B eqn:H5.
  assert (forall x y, B :(x,y): <-> A :(x,y): /\ Minimal r (c x) y) as H6. {
    intros x y. split; intros H6.
    - rewrite H5 in H6. destruct H6 as [u [v [H6 H7]]].
      apply OrdPair.Equal in H6. destruct H6 as [H6 H8]. subst. assumption.
    - rewrite H5. exists x, y. split. 2: assumption. reflexivity. }
  assert (Functional B) as H7. {
    intros x y1 y2 H7 H8. apply H6 in H7. apply H6 in H8.
    destruct H7 as [H7 H9]. destruct H8 as [H8 H10].
    apply Minimal.IsUnique with r b (c x); try assumption.
    rewrite H4. apply Specify.IsInclL. }
  assert (toClass a :<=: domain B) as H8. {
    intros x H8.
    assert (c x :<=: b) as H9. {
      rewrite H4. apply Specify.IsInclL. }
    assert (c x <> :0:) as H10. {
      apply Empty.HasElem. rewrite H4. specialize (H2 x H8).
      destruct H2 as [y [H2 H10]]. exists y.
      apply Specify.Charac. split; assumption. }
    assert (exists y, Minimal r (c x) y) as H11. {
      apply WellOrdering.HasMinimal with b; assumption. }
    destruct H11 as [y H11]. exists y. apply H6. split. 2: assumption.
    assert (A :(x,y):) as X. 2: apply X.
    apply (Specify.IsInclR (fun y => A:(x,y):) b).
    assert (y :< c x) as H12. { apply Minimal.IsIn with r. assumption. }
    rewrite H4 in H12. assumption. }
  remember (B:|:a) as f eqn:H9.
  assert (FunctionOn f a) as H10. {
    rewrite H9. apply RestrictOfClass.IsFunctionOn; assumption. }
  assert (forall x, x :< a -> A :(x,f!x):) as H11. {
    intros x H11.
    assert (f!x = B!x) as H12. {
      rewrite H9. apply RestrictOfClass.Eval; assumption. }
    assert (B:(x,f!x):) as H13. {
      rewrite H12. apply EvalOfClass.Satisfies. 1: assumption.
      apply H8. assumption. }
    apply H6 in H13. apply H13. }
  exists f. split; assumption.
Qed.

