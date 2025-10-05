Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.FunctionOn.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CIN := ZF.Class.Incl.
Module COC := ZF.Class.Ordinal.Core.
Module CRF := ZF.Class.Relation.Function.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRR := ZF.Class.Relation.Range.

Module SIN := ZF.Set.Incl.
Module SOC := ZF.Set.Ordinal.Core.
Module SRR := ZF.Set.Relation.Range.

(* With appropriate assumptions, this is the function class which given a       *)
(* function y, selects the smallest 'fresh' value z of A, i.e. the smallest     *)
(* element z of A which has not yet been 'used' by y.                           *)
Definition SmallestFresh (R A:Class) : Class := fun x =>
  exists y z, x = :(y,z): /\ Minimal R (A :\: toClass (SRR.range y)) z.

Proposition Charac2 : forall (R A:Class) (y z:U),
  SmallestFresh R A :(y,z): <-> Minimal R (A :\: toClass (SRR.range y)) z.
Proof.
  intros R A y z. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]]. apply OrdPair.WhenEqual in H1.
    destruct H1 as [H1 H3]. subst. assumption.
  - exists y. exists z. split. 1: reflexivity. assumption.
Qed.

Proposition IsFunctional : forall (R A:Class),
  Total R A -> Functional (SmallestFresh R A).
Proof.
  intros R A H1 x y1 y2 H2 H3.
  apply Charac2 in H2. apply Charac2 in H3. revert H2 H3.
  apply Minimal.Unique with A. 1: assumption. apply Class.Inter2.IsInclL.
Qed.

Proposition IsRelation : forall (R A:Class), Relation (SmallestFresh R A).
Proof.
  intros R A x H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

Proposition IsFunction : forall (R A:Class),
  Total R A -> Function (SmallestFresh R A).
Proof.
  intros R A H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Lemma IsMinimal : forall (R A F:Class) (x:U),
  WellFoundedWellOrd R A                        ->
  F :~: SmallestFresh R A                       ->
  (A :\: toClass (SRR.range x)) :<>: :0:        ->
  Minimal R (A :\: toClass (SRR.range x)) F!x.
Proof.
  intros R A F x H1 H2 H3.
  assert (exists y, Minimal R (A :\: toClass (range x)) y) as H4. {
    apply WellFoundedWellOrd.HasMinimal with A; try assumption.
    apply Class.Inter2.IsInclL. }
  destruct H4 as [y H4].
  assert (F!x = y) as H5. {
    apply CRF.EvalCharac.
    - apply CRF.EquivCompat with (SmallestFresh R A).
      + apply Equiv.Sym. assumption.
      + apply IsFunction, H1.
    - exists y. apply H2, Charac2. assumption.
    - apply H2, Charac2. assumption. }
  rewrite H5. assumption.
Qed.

Proposition WhenSmallestFreshValue : forall (R A F G:Class),
  WellFoundedWellOrd R A                  ->
  F :~: SmallestFresh R A                 ->
  CFO.FunctionOn G On                     ->
  (forall a, On a -> G!a = F!(G:|:a))     ->

  (forall a,
    On a                                  ->
    (A :\: toClass G:[a]:) :<>: :0:       ->
    Minimal R (A :\: toClass G:[a]:) G!a
  ).
Proof.
  intros R A F G H1 H2 H3 H4 a H5 H6.
  assert (SRR.range (G:|:a) = G:[a]:) as H7. {
    apply RestrictOfClass.RangeOf, H3. }
  rewrite H4. 2: assumption. rewrite <- H7.
  apply IsMinimal; try assumption. rewrite H7. assumption.
Qed.

Proposition IsIsom : forall (R A F G:Class),
  WellFoundedWellOrd R A                ->
  Proper A                              ->
  F :~: SmallestFresh R A               ->
  CFO.FunctionOn G On                   ->
  (forall a, On a -> G!a = F!(G:|:a))   ->
  Isom G E R On A.
Proof.
  intros R A F G H1 H2 H3 H4 H5.
  assert (forall a, On a -> (A :\: toClass G:[a]:) :<>: :0:) as H6. {
    intros a H6. apply Diff.MinusASet. assumption. }
  assert (forall a, On a -> Minimal R (A :\: toClass G:[a]:) G!a) as H7. {
    intros a H7. apply WhenSmallestFreshValue with F; try assumption.
    apply H6. assumption. }
  assert (forall a, On a -> (A :\: toClass G:[a]:) G!a) as H8. {
    intros a H8. apply Minimal.IsIn with R, H7. assumption. }
  assert (CRR.range G :<=: A) as H9. { apply WhenFreshValue; assumption. }
  assert (OneToOne G) as H10. { apply (WhenFreshValue G A); assumption. }
  assert (Proper (CRR.range G)) as H11. {
    intros H11.
    assert (Small On) as H12. {
      apply CFO.DomainIsSmall with G; assumption. }
    revert H12. apply COC.OnIsProper. }
  assert ( A :~: CRR.range G
    \/ exists a, A a /\ CRR.range G :~: initSegment R A a) as H12. {
    apply WellFoundedWellOrd.IsAllOrInitSegment; try assumption.
    intros x y H12 H13 H14.
    assert (exists a, On a /\ G!a = y) as H15. {
      apply CFO.RangeCharac; assumption. }
    destruct H15 as [a [H15 H16]].
    assert (Minimal R (A :\: toClass G:[a]:) G!a) as H17. {
      apply WhenSmallestFreshValue with F; try assumption.
      apply Diff.MinusASet. assumption. }
    destruct H17 as [H17 H18].
    assert (~ (A :\: toClass G:[a]:) x) as H19. {
      intros H19. revert H14. rewrite <- H16. apply H18. assumption. }
    assert (x :< G:[a]:) as H20. {
      apply DoubleNegation. intros H20. apply H19. split; assumption. }
      apply ImageByClass.ToClass in H20. 2: apply H4.
      destruct H20 as [u [H20 H21]]. exists u. assumption. }
  assert (A :~: CRR.range G) as H13. {
    destruct H12 as [H12|H12]. 1: assumption. destruct H12 as [a [H12 H13]].
    exfalso. apply H11. apply Small.EquivCompat with (initSegment R A a).
    - apply Equiv.Sym. assumption.
    - apply H1. assumption. }
  assert (Bij G On A) as H14. {
    split.
    - split. 2: apply H4. split. 2: assumption. apply H4.
    - apply Equiv.Sym. assumption. }
  assert (forall a b, On a -> On b -> a :< b -> R :(F!a,F!b):) as H15. {
    intros a b H15 H16 H17.
    assert (A G!a) as G1. {
      apply H9. exists a. apply CFO.Satisfies with On; assumption. }
    assert (A G!b) as G2. {
      apply H9. exists b. apply CFO.Satisfies with On; assumption. }
    assert (G:[a]: :<=: G:[b]:) as H18. {
      apply ImageByClass.InclCompatR. 1: apply H4.
      apply SOC.ElemIsIncl; assumption. }
    assert (A :\: toClass G:[b]: :<=: A :\: toClass G:[a]:) as H19. {
      apply Diff.InclCompatR. assumption. }
    assert ((A :\: toClass G:[a]:) G!b) as H20. {
      apply H19. apply Minimal.IsIn with R. apply H7. assumption. }
    assert (G!a = G!b \/ R :(G!a,G!b):) as H21. {
      assert (G!a = G!b \/ R :(G!a,G!b): \/ R :(G!b,G!a):) as H21. {
        apply H1; assumption. }
Admitted.
