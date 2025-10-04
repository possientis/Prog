Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CRF := ZF.Class.Relation.Function.

(* In spirit, this is the function class which given a function y selects the   *)
(* smallest 'fresh' value z of A, i.e. which has not yet been 'used' by y.      *)
Definition SmallestFresh (R A:Class) : Class := fun x =>
  exists y z, x = :(y,z): /\ Minimal R (A :\: toClass (range y)) z.

Proposition Charac2 : forall (R A:Class) (y z:U),
  SmallestFresh R A :(y,z): <-> Minimal R (A :\: toClass (range y)) z.
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
  WellFoundedWellOrd R A                    ->
  F :~: SmallestFresh R A                   ->
  (A :\: toClass (range x)) :<>: :0:        ->
  Minimal R (A :\: toClass (range x)) F!x.
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
  FunctionOn G On                         ->
  (forall a, On a -> G!a = F!(G:|:a))     ->

  (forall a,
    On a                                  ->
    (A :\: toClass G:[a]:) :<>: :0:       ->
    Minimal R (A :\: toClass G:[a]:) G!a
  ).
Proof.
  intros R A F G H1 H2 H3 H4 a H5 H6.
  assert (range (G:|:a) = G:[a]:) as H7. { apply RestrictOfClass.RangeOf, H3. }
  rewrite H4. 2: assumption. rewrite <- H7.
  apply IsMinimal; try assumption. rewrite H7. assumption.
Qed.

Proposition IsIsom : forall (R A F G:Class),
  WellFoundedWellOrd R A                ->
  Proper A                              ->
  F :~: SmallestFresh R A               ->
  FunctionOn G On                       ->
  (forall a, On a -> G!a = F!(G:|:a))   ->
  Isom G E R On A.
Proof.
  intros R A F G H1 H2 H3 H4 H5.
  assert (forall a, On a -> (A :\: toClass G:[a]:) :<>: :0:) as H6. {
Admitted.
