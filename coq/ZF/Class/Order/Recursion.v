Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Minimal.
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
Require Import ZF.Set.Relation.RestrictOfClass.

Module COI := ZF.Class.Order.InitSegment.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CFL := ZF.Class.Relation.Functional.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRR := ZF.Class.Relation.Relation.

Module SIN := ZF.Set.Incl.
Module SOI := ZF.Set.Order.InitSegment.
Module SRD := ZF.Set.Relation.Domain.
Module SRF := ZF.Set.Relation.Function.
Module SFL := ZF.Set.Relation.Functional.
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

Lemma Restrict : forall (R A F:Class) (a f:U),
  WellFoundedWellOrd R A                                                ->
  A a                                                                   ->
  (forall b, b :< initSegment R A a -> CRD.domain (Recursion R A F) b)  ->
  f = (Recursion R A F) :|: initSegment R A a                           ->
  K R A F f a.
Proof.
  intros R A F a f H1 H2 H3 H4.
  remember (CRD.domain (Recursion R A F)) as B eqn:H5.
  assert (WellFounded R A) as H6. { apply H1. }
  assert (Transitive R A) as H7. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (A :<=: A) as H8. { apply Class.Incl.Refl. }
  assert (SRD.domain f = initSegment R A a) as H9. {
    apply SIN.DoubleInclusion. split; intros x H9.
    - apply SRD.Charac in H9. destruct H9 as [y H9]. rewrite H4 in H9.
      apply RestrictOfClass.Charac2 in H9.
      + apply H9.
      + apply IsFunction. assumption.
    - assert (H10 := H9).
      apply H3 in H9. rewrite H5 in H9. destruct H9 as [y H9].
      apply SRD.Charac. exists y. rewrite H4.
      apply RestrictOfClass.Charac2Rev; try assumption.
      apply IsFunction. assumption. }
  assert (SRR.Relation f) as H10. {
    rewrite H4. apply RestrictOfClass.IsRelation, IsFunction. assumption. }
  assert (SFL.Functional f) as H11. {
    rewrite H4. apply RestrictOfClass.IsFunctional, IsFunction. assumption. }
  assert (SRF.Function f) as H12. { split; assumption. }
  assert (SFO.FunctionOn f (initSegment R A a)) as H13. { split; assumption. }
  assert (forall b,
    b :< initSegment R A a -> f!b = F!(f:|:initSegment R A b)) as H14. {
    intros b H14.
    remember (Recursion R A F) as G eqn:H15.
    assert (A b) as H16. { apply (SOI.WhenIn R A A a); assumption. }
    assert (R :(b,a):) as H17. { apply (SOI.IsLess R A A a b); assumption. }
    assert (B b) as H18. { apply H3. assumption. }
    assert (G :(b,G!b):) as H19. {
      apply CRF.Satisfies.
      - rewrite H15. apply IsFunction. assumption.
      - rewrite H5 in H18. assumption. }
    assert (exists g c, :(b,G!b): :< g /\ K R A F g c) as H20. {
      apply (proj1 (Charac2 _ _ _ _ _ )). rewrite H15.
      rewrite H15 in H19. assumption. }
    destruct H20 as [g [c [H20 H21]]].
    assert (H22 := H21). destruct H22 as [H22 [[H23 H24] H25]].
    assert (b :< domain g) as H26. { apply SRD.Charac. exists G!b. assumption. }
    assert (R :(b,c):) as H27. {
        rewrite H24 in H26. apply (SOI.IsLess R A A) in H26; assumption. }
    assert (f!b = g!b) as H28. {
      assert (g!b = G!b) as H28. { apply SRF.EvalCharac; assumption. }
      assert (f!b = G!b) as H29. {
        rewrite H4. apply RestrictOfClass.Eval. 2: assumption.
        rewrite H15. apply IsFunction. assumption. }
        rewrite H28, H29. reflexivity. }
    assert (forall x, x :< initSegment R A b -> f!x = g!x) as H29. {
      intros x H29.
      assert (g!x = G!x) as H30. {
        assert (:(x,g!x): :< g) as H30. {
          apply SRF.Satisfies. 1: assumption. rewrite H24.
          apply (SOI.WhenLess R A A b c); assumption. }
        assert (G :(x,g!x):) as H31. {
          rewrite H15. apply Charac2. exists g. exists c. split; assumption. }
        symmetry. apply CRF.EvalCharac. 3: assumption.
        - rewrite H15. apply IsFunction. assumption.
        - exists g!x. assumption. }
      assert (f!x = G!x) as H31. {
        rewrite H4. apply RestrictOfClass.Eval.
        - rewrite H15. apply IsFunction. assumption.
        - apply (SOI.WhenLess R A A b); assumption. }
      rewrite H30, H31. reflexivity. }
    assert (f:|:initSegment R A b = g :|: initSegment R A b) as H32. {
      apply Function.RestrictEqual; try assumption; intros x H32.
      - rewrite H9. apply (SOI.WhenLess R A A b); assumption.
      - rewrite H24. apply (SOI.WhenLess R A A b); assumption. }
    rewrite H28, H32. apply H25. rewrite <- H24. assumption. }
  split. 1: assumption. split; assumption.
Qed.

Proposition DomainIsA : forall (R A F:Class), WellFoundedWellOrd R A ->
  CRD.domain (Recursion R A F) :~: A.
Proof.
  intros R A F H1.
  remember (CRD.domain (Recursion R A F)) as B eqn:H2.
  assert (WellFounded R A) as H3. { apply H1. }
  assert (Transitive R A) as H1'. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (A :<=: A) as H4. { apply Class.Incl.Refl. }
  assert (B :<=: A) as H5. {
    rewrite H2. intros x [y H5]. destruct H5 as [f [a [H5 [H6 [[_ H7] _]]]]].
    assert (x :< domain f) as H8. {
      apply SRD.Charac. exists y. assumption. }
    rewrite H7 in H8. apply SOI.WhenIn with R A a; assumption. }
  assert (forall a, A a -> B a) as H6. {
    apply Induction' with R. 1: assumption.
    intros c H6 H7.
    remember (Recursion R A F :|: initSegment R A c) as f eqn:H8.
    assert (K R A F f c) as H9. {
      apply Restrict; try assumption.
      intros b H9. rewrite <- H2. apply H7.
      apply (SOI.ToClass R A A) in H9; assumption. }
Admitted.
