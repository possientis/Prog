Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.EvalAsClass.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Max.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Truncate.
Require Import ZF.Set.UnionGen.
Require Import ZF.Set.UnionGenOfClass.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CIN := ZF.Class.Incl.
Module CPR := ZF.Class.Prod.
Module CRI := ZF.Class.Relation.Image.
Module SOR := ZF.Set.Ordinal.RecursionNOfClass.

(* R is closed on A.                                                            *)
Definition Closed (R A:Class) : Prop := R:[A]: :<=: A.

(* R is closed on A^2.                                                          *)
Definition Closed2 (R A:Class) : Prop := R:[A:x:A]: :<=: A.

Proposition Exists : forall (R S A:Class) (p q a:U),
  p :< :N                                                                   ->
  q :< :N                                                                   ->
  toClass a :<=: A                                                          ->
  (forall i, i :< p -> Closed  R$i A)                                       ->
  (forall i, i :< q -> Closed2 S$i A)                                       ->
  (forall i x, i :< p -> toClass x :<=: A -> Small R$i:[toClass x      ]:)  ->
  (forall i x, i :< q -> toClass x :<=: A -> Small S$i:[toClass (x:x:x)]:)  ->
  exists b,
    a :<=: b                                        /\
    toClass b :<=: A                                /\
    (forall i, i :< p -> Closed  R$i (toClass b))   /\
    (forall i, i :< q -> Closed2 S$i (toClass b)).
Proof.
  intros R S A p q a H1 H2 H3 H4 H5 H6 H7.
  remember (fun i x => truncate (R$i:[toClass x]:)) as R_ eqn:H8.
  remember (fun i x => truncate (S$i:[toClass (x:x:x)]:)) as S_ eqn:H9.
  remember (fun x => :\/:_{p} (toFun (fun i => R_ i x))) as R' eqn:H10.
  remember (fun x => :\/:_{q} (toFun (fun i => S_ i x))) as S' eqn:H11.
  remember (fun x => x :\/: R' x :\/: S' x) as G eqn:H12.
  remember (SOR.recursion (toFun G) a) as f eqn:H13.
  remember (:\/:_{:N} f) as b eqn:H14.
  exists b.
  assert (:0: :< :N) as G0. { apply Omega.HasZero. }
  assert (domain f = :N) as G1. { rewrite H13. apply SOR.IsFunctionOn. }
  assert (Functional f) as G2. { rewrite H13. apply SOR.IsFunctionOn. }
  assert (forall x, x :< b <-> exists n, n :< :N /\ x :< f!n) as G3. {
    rewrite H14. apply UnionGen.Charac. }
  assert (forall n, n :< :N -> f!n :<=: b) as G4. {
    intros n G4 x G5. apply G3. exists n. split; assumption. }
  assert (a = f!:0:) as G5. { rewrite H13, SOR.WhenZero. reflexivity. }
  assert (forall n, n :< :N -> f!(succ n) = f!n :\/: R' f!n :\/: S' f!n) as G6. {
    intros n G6. rewrite H13, SOR.WhenSucc, <- H13, ToFun.Eval, H12.
    2: assumption. reflexivity. }
  assert (forall x, toClass x :<=: A -> toClass (R' x) :<=: A) as G7. {
    intros c G7. rewrite H10. apply UnionGenOfClass.WhenClassBounded.
    intros i G8. rewrite ToFun.Eval, H8.
    apply Truncate.IsIncl. apply CIN.Tran with R$i:[A]:.
    - apply CRI.InclCompatR. assumption.
    - apply H4. assumption. }
  assert (forall x, toClass x :<=: A -> toClass (S' x) :<=: A) as G8. {
    intros x G8. rewrite H11. apply UnionGenOfClass.WhenClassBounded.
    intros i G9. rewrite ToFun.Eval, H9.
    apply Truncate.IsIncl. apply CIN.Tran with S$i:[A:x:A]:.
    - apply CRI.InclCompatR.
      apply CIN.EquivCompatL with (toClass x :x: toClass x).
      + apply Equiv.Sym, Prod.ToClass.
      + apply CPR.InclCompat; assumption.
    - apply H5. assumption. }
  assert (forall n, n :< :N -> f!n :<=: f!(succ n)) as G9. {
    intros n G9. rewrite G6. 2: assumption.  apply Union2.IsInclL. }
  assert (forall n m, n :< :N -> m :< :N -> n :<=: m -> f!n :<=: f!m) as G10. {
    intros n m G10. revert m. apply Omega.Induction'. 1: assumption.
    - apply Incl.Refl.
    - intros m G11 G12 G13. apply Incl.Tran with f!m. 1: assumption.
      apply G9. assumption. }

  assert (forall n, n :< :N -> R' f!n :\/: S' f!n :<=: f!(succ n)) as H16. {
    intros n H16. rewrite G6. 2: assumption.  apply Union2.IsInclR. }
  assert (forall n, n :< :N -> R' f!n :<=: f!(succ n)) as H17. {
    intros n H17.
    apply Incl.Tran with (R' f!n :\/: S' f!n).
    - apply Union2.IsInclL.
    - apply H16. assumption. }
  assert (forall n, n :< :N -> S' f!n :<=: f!(succ n)) as H18. {
    intros n H18.
    apply Incl.Tran with (R' f!n :\/: S' f!n).
    - apply Union2.IsInclR.
    - apply H16. assumption. }
  assert (a :<=: b) as H19. { rewrite G5. apply G4. assumption. }
  assert (forall n, n :< :N -> toClass f!n :<=: A) as H20. {
    apply Omega.Induction.
    - rewrite <- G5. assumption.
    - intros n H20 IH. rewrite G6. 2: assumption. intros x H21.
      apply Union2.Charac3 in H21. destruct H21 as [H21|[H21|H21]].
      + apply IH. assumption.
      + apply (G7 f!n); assumption.
      + apply (G8 f!n); assumption. }
  assert (toClass b :<=: A) as H21. {
    intros x H21. apply G3 in H21. destruct H21 as [n [H21 H22]].
    apply H20 with n; assumption. }
  assert (forall i, i :< p -> Closed R$i (toClass b)) as H22. {
    intros i H22 y H23. destruct H23 as [x [H23 H24]].
    apply G3 in H23. destruct H23 as [n [H23 H25]].
    assert (succ n :< :N) as K1. { apply Omega.HasSucc. assumption. }
    apply G4 with (succ n). 1: assumption. rewrite G6. 2: assumption.
    apply Union2.Charac3. right. left. rewrite H10.
    apply UnionGenOfClass.Charac. exists i. split. 1: assumption.
    rewrite ToFun.Eval, H8. apply Truncate.Charac. split.
    - apply H6. 1: assumption. apply H20. assumption.
    - exists x. split; assumption. }
  assert (forall i, i :< q -> Closed2 S$i (toClass b)) as H23. {
    intros i H23 y H24. destruct H24 as [x [H24 H25]].
    destruct H24 as [u [v [H24 [H26 H27]]]].
    apply G3 in H26. destruct H26 as [n [H26 H28]].
    apply G3 in H27. destruct H27 as [m [H27 H29]].
    remember (n :\/: m) as r eqn:H30.
    assert (r :< :N) as K1. { rewrite H30. apply Omega.HasMax; assumption. }
    assert (succ r :< :N) as K2. { apply Omega.HasSucc. assumption. }
    assert (n :<=: r) as H31. { rewrite H30. apply Union2.IsInclL. }
    assert (m :<=: r) as H32. { rewrite H30. apply Union2.IsInclR. }
    assert (u :< f!r) as H33. { apply (G10 n r); assumption. }
    assert (v :< f!r) as H34. { apply (G10 m r); assumption. }
    apply G4 with (succ r). 1: assumption. rewrite G6. 2: assumption.
    apply Union2.Charac3. right. right. rewrite H11.
    apply UnionGenOfClass.Charac. exists i. split. 1: assumption.
    rewrite ToFun.Eval, H9. apply Truncate.Charac. split.
    - apply H7. 1: assumption. apply H20. assumption.
    - exists x. split. 2: assumption. rewrite H24.
      apply Prod.Charac2. split; assumption. }
  split. 1: assumption. split. 1: assumption. split; assumption.
Qed.

