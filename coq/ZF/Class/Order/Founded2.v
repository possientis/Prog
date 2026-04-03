Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.


(* If R is founded on A, there is no decreasing loop of elements of A.          *)
Proposition NoLoopDec : forall (R A:Class), Founded R A ->
  ~ exists n f,
    n :< :N                                       /\
    :1: :<=: n                                    /\
    FunctionOn f (succ n)                         /\
    f!:0: = f!n                                   /\
    (forall i, i :< succ n -> A f!i)              /\
    (forall i, i :< n -> R :(f!(succ i),f!i):).
Proof.
  intros R A H1 [n [f [H2 [H3 [H4 [H5 [H6 H7]]]]]]].
  remember (range f) as a eqn:H8.
  assert (domain f = succ n) as G1. { apply H4. }
  assert (forall i, i :< succ n -> f!i :< a) as G2. {
    intros i G2. rewrite H8. apply Range.Charac. exists i.
    apply FunctionOn.Satisfies with (succ n); assumption. }
  assert (forall y, y :< a -> exists i, i :< succ n /\ f!i = y) as G3. {
    intros y G3. rewrite H8 in G3. apply Range.Charac in G3.
    destruct G3 as [i G3]. exists i.
    assert (i :< domain f) as H9. { apply Domain.Charac. exists y. assumption. }
    rewrite G1 in H9.
    assert (f!i = y) as H10. {
      apply (FunctionOn.Eval f (succ n)); assumption. }
    split; assumption. }
  assert (toClass a :<=: A) as H9. {
    intros y H9. specialize (G3 y H9). destruct G3 as [i [G3 G4]].
    rewrite <- G4. apply H6. assumption. }
  assert (a <> :0:) as H12. {
    apply Empty.HasElem. exists f!:0:. apply G2.
    apply Omega.SuccHasZero. assumption. }
  assert (exists m, Minimal R (toClass a) m) as H13. { apply H1; assumption. }
  destruct H13 as [m H13].
  assert (forall i, i :< n -> ~ Minimal R (toClass a) f!i) as H14. {
    intros i H14 H15. specialize (H7 i H14). revert H7. apply H15, G2.
    apply Omega.SuccElemCompat; try assumption.
    apply Omega.IsIn with n; assumption. }
  assert (forall i, i :< succ n -> ~ Minimal R (toClass a) f!i) as H15. {
    intros i H15. apply Union2.Charac in H15.
    destruct H15 as [H15|H15].
    - apply H14. assumption.
    - apply Single.Charac in H15. rewrite H15, <- H5. apply H14, H3.
      apply Succ.IsIn. }
  assert (m :< a) as H16. { apply (Minimal.IsIn R (toClass a)). assumption. }
  specialize (G3 m H16). destruct G3 as [i [G3 G4]].
  specialize (H15 i G3). apply H15. rewrite G4. assumption.
Qed.
