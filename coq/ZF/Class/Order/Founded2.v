Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OfMinRank.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Rank.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.
Require Import ZF.Set.UnionGen.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Module CIN := ZF.Class.Incl.
Module COI := ZF.Class.Order.InitSegment.
Module SOR := ZF.Set.Ordinal.RecursionNOfClass.
Module SUG := ZF.Set.UnionGenOfClass.

Proposition HasMinimal : forall (R A B:Class),
  Founded R A                 ->
  B :<=: A                    ->
  B :<>: :0:                  ->
  exists x, Minimal R B x.
Proof.
  intros R A B H1 H2 H3. apply Classic.NotForAllNot. intros H4.
  assert (forall x, B x -> exists y, B y /\ R :(y,x):) as H5. {
    intros x H5. apply Minimal.NotMinimal. 1: assumption. apply H4. }
  remember (fun y => ofMinRank (initSegment R B y)) as G eqn:H6.
  remember (fun a => :\/:_{a} :[G]:) as F eqn:H7.
  remember (SOR.recursion :[F]: (ofMinRank B)) as f eqn:H8.
  remember (:\/:_{:N} f) as b eqn:H9.
  assert (FunctionOn f :N) as H10. { rewrite H8. apply SOR.IsFunctionOn. }
  assert (f!:0: = ofMinRank B) as H11. {
    rewrite H8. apply SOR.WhenZero. }
  assert (forall n, n :< :N -> f!(succ n) = :\/:_{f!n} :[G]:) as H12. {
    intros n H12. rewrite H8, SOR.WhenSucc, <- H8, ToFun.Eval, H7.
    2: assumption. reflexivity. }
  assert (forall y, initSegment R B y :<=: B) as H13. {
    intros y. apply COI.IsIncl. }
  assert (forall y, :[G]:!y = ofMinRank (initSegment R B y)) as H14. {
    intros y. rewrite ToFun.Eval, H6. reflexivity. }
  assert (forall n, n :< :N -> toClass f!n :<=: B) as H15. {
    intros n H15.
    assert (n = :0: \/ :0: :< n) as H16. { apply Omega.ZeroOrElem. assumption. }
    destruct H16 as [H16|H16].
    - rewrite H16, H11. apply OfMinRank.IsIncl.
    - remember :U(n) as m eqn:H17.
      assert (succ m = n) as H18. {
        rewrite H17. apply Omega.SuccOfUnion; assumption. }
      assert (m :< :N) as H19. {
        apply Omega.HasSuccRev. rewrite H18. assumption. }
      rewrite <- H18, H12. 2: assumption.
      apply SUG.WhenClassBounded.
      intros y _. rewrite H14.
      apply CIN.Tran with (initSegment R B y).
      + apply OfMinRank.IsIncl.
      + apply H13. }
  assert (toClass b :<=: B) as H16. {
    rewrite H9. intros y H16. apply UnionGen.Charac in H16.
    destruct H16 as [n [H16 H17]]. apply (H15 n); assumption. }
  assert (f!:0: <> :0:) as H17. {
    rewrite H11. apply OfMinRank.IsNotEmpty. assumption. }
  assert (b <> :0:) as H18. {
    rewrite H9. apply Empty.HasElem in H17. destruct H17 as [x H17].
    apply Empty.HasElem. exists x. apply UnionGen.Charac.
    exists :0:. split. 2: assumption. apply Omega.HasZero. }
  assert (exists a, Minimal R (toClass b) a) as H19. {
    apply H1. 2: assumption. apply CIN.Tran with B; assumption. }
  destruct H19 as [a [H19 H20]].
  rewrite H9 in H19. apply UnionGen.Charac in H19. destruct H19 as [n [H19 H21]].
  assert (B a) as H22. { apply (H15 n); assumption. }
  specialize (H5 a H22). destruct H5 as [y [H5 H23]].
  assert (initSegment R B a :<>: :0:) as H24. {
    apply CEM.HasElem. exists y. apply COI.Charac. split; assumption. }
  assert (ofMinRank (initSegment R B a) <> :0:) as H25. {
    apply OfMinRank.IsNotEmpty. assumption. }
  apply Empty.HasElem in H25. destruct H25 as [z H25].
  assert (R :(z,a):) as H26. {
    apply COI.IsLess with B. apply OfMinRank.IsIncl. assumption. }
  assert (z :< b) as H27. {
    rewrite H9. apply UnionGen.Charac. exists (succ n). split.
    - apply Omega.HasSucc. assumption.
    - rewrite H12. 2: assumption.
      apply SUG.Charac. exists a. split. 1: assumption.
      rewrite H14. assumption. }
  apply (H20 z); assumption.
Qed.

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
      apply (FunctionOn.Eval' f (succ n)); assumption. }
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
