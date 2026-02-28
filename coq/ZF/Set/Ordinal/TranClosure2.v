Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CIN := ZF.Class.Incl.
Module CRC := ZF.Class.Relation.Converse.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CRL := ZF.Class.Relation.Functional.
Module CRR := ZF.Class.Relation.Relation.
Module SOR := ZF.Set.Ordinal.RecursionNOfClass.

(* An R-transitive set a in class A,                                            *)
Definition Transitive (R A:Class) (a:U) : Prop :=
  forall x y, A x -> R :(x,y): -> y :< a -> x :< a.

Proposition Exists : forall (R A:Class) (a:U),
  WellFounded R A   ->
  toClass a :<=: A  ->
  exists b,
    a :<=: b                                              /\
    toClass b :<=: A                                      /\
    Transitive R A b                                      /\
    (forall x, x :< b -> exists n g,
      Fun g (succ n) b                            /\
      g!:0: :< a                                  /\
      g!n = x                                     /\
      (forall i, i :< n -> R :(g!(succ i),g!i):))         /\
    (forall c,
      a :<=: c          ->
      toClass c :<=: A  ->
      Transitive R A c  ->
      b :<=: c).
Proof.
  intros R A a H1 H2.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  remember (fun y => exists x, A x /\ y = :(x,initSegment R A x):) as B eqn:H3.
  assert (forall x y, B :(x,y): <-> A x /\ y = initSegment R A x) as H4. {
    intros x y. split; intros H4.
    - rewrite H3 in H4. destruct H4 as [u [H4 H5]].
      apply OrdPair.WhenEqual in H5. destruct H5 as [H5 H6]. subst.
      split. 1: assumption. reflexivity.
    - rewrite H3. destruct H4 as [H4 H5]. exists x. split. 1: assumption.
      rewrite H5. reflexivity. }
  assert (CRR.Relation B) as H5. {
    intros y H5. rewrite H3 in H5. destruct H5 as [x [H5 H6]].
    exists x, (initSegment R A x). assumption. }
  assert (CRL.Functional B) as H6. {
    intros x y1 y2 H6 H7.
    apply H4 in H6. destruct H6 as [H6 H8].
    apply H4 in H7. destruct H7 as [H7 H9].
    subst. reflexivity. }
  assert (CRF.Function B) as H7. { split; assumption. }
  assert (CRD.domain B :~: A) as H8. {
    intros x. split; intros H8.
    - destruct H8 as [y H8]. apply H4 in H8. apply H8.
    - exists (initSegment R A x). apply H4. split. 1: assumption. reflexivity. }
  assert (forall x, A x -> B!x = initSegment R A x) as H9. {
    intros x H9. apply EvalOfClass.Charac. 1: assumption.
    - apply H8. assumption.
    - apply H4. split. 1: assumption. reflexivity. }
  remember (fun y => A :/\: R^:-1: :[toClass y]:) as F eqn:H10.
  assert (forall y, toClass y :<=: A -> F y :~: toClass :U(B:[y]:)) as H11. {
    intros y H11 x. split; intros H12.
    - rewrite H10 in H12. destruct H12 as [H12 H13].
      destruct H13 as [z [H13 H14]]. apply CRC.Charac2 in H14.
      apply Union.Charac. exists (initSegment R A z). split.
      + apply InitSegment.CharacRev with A; try assumption.
        apply H11. assumption.
      + apply ImageByClass.CharacRev with z; try assumption.
        apply H4. split. 2: reflexivity. apply H11. assumption.
    - rewrite H10. apply Union.Charac in H12. destruct H12 as [z [H12 H13]].
      apply ImageByClass.Charac in H13. destruct H13 as [u [H13 H14]].
      2: assumption. apply H4 in H14. destruct H14 as [H14 H15].
      rewrite H15 in H12.
      apply (InitSegment.Charac R A A) in H12; try assumption.
      destruct H12 as [H12 H16]. split. 1: assumption.
      exists u. split. 1: assumption. apply CRC.Charac2Rev. assumption. }
  remember (fun x => x :\/: :U(B:[x]:)) as G eqn:H12.
  remember (SOR.recursion (toFun G) a) as f eqn:H13.
  remember (:U(f:[:N]:)) as b eqn:H14.
  exists b.
  assert (domain f = :N) as G2. { rewrite H13. apply SOR.IsFunctionOn. }
  assert (Functional f) as G3. { rewrite H13. apply SOR.IsFunctionOn. }
  assert (forall x, x :< b <-> exists n, n :< :N /\ x :< f!n) as G4. {
    intros x. split; intros G4.
    - rewrite H14 in G4. apply Union.Charac in G4.
      destruct G4 as [z [G4 G5]]. apply Image.Charac in G5.
      destruct G5 as [n [G5 G6]].
      assert (f!n = z) as G7. {
        apply Eval.Charac; try assumption. rewrite G2. assumption. }
      rewrite <- G7 in G4. exists n. split; assumption.
    - destruct G4 as [n [G4 G5]]. rewrite H14. apply Union.Charac.
      exists f!n. split. 1: assumption. apply Image.Charac.
      exists n. split. 1: assumption. apply Eval.Satisfies. 1: assumption.
      rewrite G2. assumption. }
  assert (forall n, n :< :N -> f!n :<=: b) as G5. {
    intros n G5 x G6. apply G4. exists n. split; assumption. }
  assert (a = f!:0:) as H15. { rewrite H13, SOR.WhenZero. reflexivity. }
  assert (forall n, n :< :N -> f!(succ n) = f!n :\/: :U(B:[f!n]:)) as H16. {
    intros n H16. rewrite H13, SOR.WhenSucc, <- H13, ToFun.Eval, H12.
    2: assumption. reflexivity. }
  assert (forall n, n :< :N -> f!n :<=: f!(succ n)) as H17. {
    intros n H17. rewrite H16. 2: assumption. apply Union2.IsInclL. }
  assert (forall n, n :< :N -> :U(B:[f!n]:) :<=: f!(succ n)) as H18. {
    intros n H18. rewrite H16. 2: assumption. apply Union2.IsInclR. }
  assert (forall n, n :< :N -> toClass f!n :<=: A) as H19. {
    apply Omega.Induction.
    - rewrite <- H15. assumption.
    - intros n H19 IH. rewrite H16. 2: assumption. intros x H20.
      apply Union2.Charac in H20. destruct H20 as [H20|H20].
      + apply IH. assumption.
      + apply H11 in H20. 2: assumption. rewrite H10 in H20. apply H20. }
  assert (toClass b :<=: A) as H20. {
    intros x H20. apply G4 in H20. destruct H20 as [n [H20 H21]].
    apply H19 with n; assumption. }
  assert (f!:0: :<=: b) as H21. {
    intros x H21. apply G4. exists :0:. split. 2: assumption.
    apply Omega.HasZero. }
  assert (a :<=: b) as H22. { rewrite H15. assumption. }
  assert (forall n, n :< :N -> F f!n :<=: toClass f!(succ n)) as H23. {
    intros n H23 x H24. apply H11 in H24.
    - apply H18; assumption.
    - apply H19. assumption. }
  assert (Transitive R A b) as H24. {
    intros x y H24 H25 H26. apply G4 in H26. destruct H26 as [n [H26 H27]].
    assert (succ n :< :N) as K1. { apply Omega.HasSucc. assumption. }
    assert (F f!n x) as H28. {
      rewrite H10. split. 1: assumption. exists y. split. 1: assumption.
      apply CRC.Charac2Rev. assumption. }
    assert (x :< f!(succ n)) as H29. { apply H23; assumption. }
    assert (F f!n x) as H30. {
      rewrite H10. split. 1: assumption. exists y. split. 1: assumption.
      apply CRC.Charac2Rev. assumption. }
    assert (x :< f!(succ n)) as H31. { apply H23; assumption. }
    apply G4. exists (succ n). split; assumption. }
  split. 1: assumption. split. 1: assumption. split. 1: assumption. split.
  remember (fun n =>
    forall x : U, x :< (f) ! (n) -> exists m g : U,
      Fun g (succ m) b /\
      eval g :0: :< a /\
      (g) ! (m) = x /\
      (forall i : U, i :< m -> R :( eval g (succ i), (g) ! (i) ):))
  as C eqn:E.
  assert (forall n, n :< :N -> C n) as H25. {
    apply Omega.Induction; rewrite E.
    - intros x H25. remember (:{:(:0:,x):}:) as g eqn:H26. exists :0:, g.
      assert (Fun g :1: b) as H27. {
        rewrite Natural.OneExtension.
        apply Fun.WhenSingle with x. 2: assumption.
        apply G5 with :0:. 2: assumption. apply Omega.HasZero. }
      assert (g!:0: = x) as H28. { apply Eval.WhenSingle. assumption. }
      assert (g!:0: :< a) as H29. {
        rewrite H28. rewrite <- H15 in H25. assumption. }
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      intros i H30. apply Empty.Charac in H30. contradiction.
    - intros n H25 IH.
Admitted.
