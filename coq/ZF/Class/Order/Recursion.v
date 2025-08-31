Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.ReflClosure.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.

Module COI := ZF.Class.Order.InitSegment.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRR := ZF.Class.Relation.Relation.

Module SOI := ZF.Set.Order.InitSegment.
Module SRD := ZF.Set.Relation.Domain.
Module SRF := ZF.Set.Relation.Function.
Module SFO := ZF.Set.Relation.FunctionOn.
Module SRR := ZF.Set.Relation.Relation.

(* The recursion class associated with R A F. In other words, when R is a well  *)
(* founded well ordering on A, the unique function class G defined on A by the  *)
(* recursion G(b) = F(G|initSegment R A b).                                     *)
Definition Recursion (R A F:Class) : Class := fun x => exists f a,
  x :< f                                                                  /\
  A a                                                                     /\
  FunctionOn f (initSegment R A a)                                        /\
  (forall b, b :< initSegment R A a -> f!b = F!(f:|:initSegment R A b)).

(* Binary predicate underlying the recursion class.                             *)
Definition K (R A F:Class) : U -> U -> Prop := fun f a =>
  A a                                                                     /\
  FunctionOn f (initSegment R A a)                                        /\
  (forall b, b :< initSegment R A a -> f!b = F!(f:|:initSegment R A b)).

Lemma Charac2 : forall (R A F:Class) (x y:U),
  Recursion R A F :(x,y): <-> exists f a, :(x,y): :< f /\ K R A F f a.
Proof.
  intros R A F x y. split; intros H1; destruct H1 as [f [a [H1 H2]]];
  exists f; exists a; split; assumption.
Qed.

(* Two recursive functions coincide on their common domain.                     *)
Lemma Coincide : forall (R A F:Class) (f g a b:U),
  WellFoundedWellOrd R A                                                  ->
  A a                                                                     ->
  A b                                                                     ->
  R^:=: :(a,b):                                                           ->
  FunctionOn f (initSegment R A a)                                        ->
  FunctionOn g (initSegment R A b)                                        ->
  (forall x, x :< initSegment R A a -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, x :< initSegment R A b -> g!x = F!(g:|:initSegment R A x))   ->
  (forall x, x :< initSegment R A a -> f!x = g!x).
Proof.
  intros R A F f g a b H1 H2 H3 H4 H5 H6 H7 H8. apply ReflClosure.Charac2 in H4.
  assert (forall x c, A c -> x :< initSegment R A c -> A x) as H9. {
    intros x c H9 H10. apply (SOI.IsIncl R A A c) in H10; try assumption.
    - apply H1.
    - apply Class.Incl.Refl. }
  apply Induction' with R.
  - apply WellFoundedWellOrd.WhenIncl with A. 1: assumption.
    apply SOI.IsIncl with A. 2: assumption.
    + apply H1.
    + apply Class.Incl.Refl.
  - intros c H10 H11.
    assert (Transitive R A) as H12. {
      apply WellFoundedWellOrd.IsTransitive. assumption. }
    assert (WellFounded R A) as H13. { apply H1. }
    assert (A c) as H14. {
      apply (SOI.IsIncl R A A) in H10; try assumption. apply Class.Incl.Refl. }
    assert (initSegment R A a :<=: initSegment R A b) as H15. {
      destruct H4 as [H4|H4].
      - subst. apply Incl.Refl.
      - apply SOI.WhenLess with A; try assumption. apply Class.Incl.Refl. }
    assert (c :< initSegment R A b) as H16. { apply H15. assumption. }
    specialize (H7 c H10). specialize (H8 c H16).
    assert (f :|: initSegment R A c = g :|: initSegment R A c) as H17. {
      apply FunctionOn.RestrictEqual with (initSegment R A a) (initSegment R A b);
      try assumption.
      - apply SOI.WhenLess with A; try assumption.
        + apply Class.Incl.Refl.
        + apply SOI.IsLess with A A; try assumption. apply Class.Incl.Refl.
      - apply SOI.WhenLess with A; try assumption.
        + apply Class.Incl.Refl.
        + apply SOI.IsLess with A A; try assumption. apply Class.Incl.Refl.
      - intros x H17. apply H11. apply COI.Charac. split.
        + assert (initSegment R A c :<=: initSegment R A a) as H18. {
            apply SOI.WhenLess with A; try assumption.
            * apply Class.Incl.Refl.
            * apply SOI.IsLess with A A; try assumption. apply Class.Incl.Refl. }
          apply H18. assumption.
        + apply SOI.IsLess with A A; try assumption. apply Class.Incl.Refl. }
    rewrite H7, H8, H17. reflexivity.
Qed.

(* The recursion class associated with R A F is a relation class.               *)
Proposition IsRelation : forall (R A F:Class), CRR.Relation (Recursion R A F).
Proof.
  intros R A F x H1. destruct H1 as [f [a [H1 [_ [[[H2 _] _] _]]]]].
  specialize (H2 x H1). assumption.
Qed.

(* The recursion class associated with R A F is a function class.               *)
Proposition IsFunction : forall (R A F:Class), WellFoundedWellOrd R A ->
  CRF.Function (Recursion R A F).
Proof.
  intros R A F H1. split. 1: apply IsRelation. intros x y z H2 H3.
  destruct H2 as [f [a [H2 [H4 [H5 H6]]]]].
  destruct H3 as [g [b [H3 [H7 [H8 H9]]]]].
  assert (Total R A) as H10. { apply H1. }
  assert (R^:=: :(a,b): \/ R^:=: :(b,a):) as H11. {
    apply ReflClosure.LeqOrLeq with A; assumption. }
  assert (x :< initSegment R A a) as H12. {
    destruct H5 as [_ H5]. rewrite <- H5.
    apply SRD.Charac. exists y. assumption. }
  assert (x :< initSegment R A b) as H13. {
    destruct H8 as [_ H8]. rewrite <- H8.
    apply SRD.Charac. exists z. assumption. }
  assert (f!x = y) as H14. {
    apply (SFO.EvalCharac f (initSegment R A a)); assumption. }
  assert (g!x = z) as H15. {
    apply (SFO.EvalCharac g (initSegment R A b)); assumption. }
  rewrite <- H14, <- H15. destruct H11 as [H11|H11].
  - apply Coincide with R A F a b; assumption.
  - symmetry. apply Coincide with R A F b a; assumption.
Qed.

