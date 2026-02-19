Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.Eval.

Module SOR := ZF.Set.Ordinal.RecursionNOfClass.

(* Every set has a smallest transitive superset.                                *)
Proposition Exists : forall a, exists b,
  a :<=: b                                          /\
  Transitive b                                      /\
  (forall c, a :<=: c -> Transitive c -> b :<=: c).
Proof.
  intros a.
  remember (fun x => x :\/: :U(x)) as F eqn:H1.
  remember (SOR.recursion :[F]: a) as f eqn:H2.
  remember (:\/:_{:N} f) as b eqn:H3.
  exists b.
  assert (a = f!:0:) as H4. { rewrite H2, SOR.WhenZero. reflexivity. }
  assert (f!:0: :<=: b) as H5. {
    rewrite H3. apply UnionGen.IsIncl, Omega.HasZero. }
  assert (a :<=: b) as H6. { rewrite H4. assumption. }
  assert (forall n, n :< :N -> f!(succ n) = f!n :\/: :U(f!n)) as H7. {
    intros n H7. rewrite H2, SOR.WhenSucc, <- H2, ToFun.Eval, H1.
    2: assumption. reflexivity. }
  assert (forall n, n :< :N -> f!n :<=: f!(succ n)) as H8. {
    intros n H8. rewrite H7. 2: assumption. apply Union2.IsInclL. }
  assert (forall n, n :< :N -> :U(f!n) :<=: f!(succ n)) as H9. {
    intros n H9. rewrite H7. 2: assumption. apply Union2.IsInclR. }
  assert (Transitive b) as H10. {
    intros x y H10 H11. rewrite H3 in H11. apply UnionGen.Charac in H11.
    destruct H11 as [n [H11 H12]].
    assert (x :< :U(f!n)) as H13. {
      apply Union.Charac. exists y. split; assumption. }
    apply H9 in H13. 2: assumption. rewrite H3.
    apply UnionGen.Charac.
    exists (succ n). split. 2: assumption.
    apply Omega.HasSucc. assumption. }
  split. 1: assumption. split. 1: assumption.
  intros c H11 H12.
  assert (forall n, n :< :N -> f!n :<=: c) as H13. {
    apply Omega.Induction.
    - rewrite <- H4. assumption.
    - intros n H13 IH.
      assert (:U(f!n) :<=: c) as H14. {
        intros x H14. apply Union.Charac in H14. destruct H14 as [y [H14 H15]].
        apply H12 with y. 1: assumption. apply IH. assumption. }
      rewrite H7. 2: assumption. apply Union2.IsIncl; assumption. }
  intros x H14. rewrite H3 in H14. apply UnionGen.Charac in H14.
  destruct H14 as [n [H14 H15]].
Admitted.
