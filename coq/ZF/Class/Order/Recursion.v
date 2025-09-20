Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Maximal.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.ReflClosure.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Order.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

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
(* founded well ordering on A and A has no maximal element, the unique function *)
(* class G defined on A by the recursion G(b) = F(G|initSegment R A b).         *)
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

Definition KExt (R A F:Class) : U -> U -> Prop := fun f a =>
  A a                                                                       /\
  FunctionOn f (initSegment R^:=: A a)                                      /\
  (forall b, b :< initSegment R^:=: A a -> f!b = F!(f:|:initSegment R A b)).

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

(* See stronger result below.                                                   *)
Lemma Restrict_ : forall (R A F:Class) (a f:U),
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
    assert (A b) as H16. { apply (SOI.IsIn R A A a); assumption. }
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

Lemma Extend : forall (R A F:Class) (a f g:U),
  WellFoundedWellOrd R A      ->
  K R A F f a                 ->
  g = f :\/: :{ :(a,F!f): }:  ->
  KExt R A F g a.
Proof.
  intros R A F a f g H1 [H2 [H3 H4]] H5. split. 1: assumption.
  assert (domain f = initSegment R A a) as G1. { apply H3. }
  assert (WellFounded R A) as G2. { apply H1. }
  assert (A :<=: A) as G3. { apply Class.Incl.Refl. }
  assert (SFO.FunctionOn g (initSegment R^:=: A a)) as G4. {
  - assert (SRR.Relation g) as H6. {
      intros x H6. rewrite H5 in H6. apply Union2.Charac in H6.
      destruct H6 as [H6|H6].
      - apply H3. assumption.
      - apply Single.Charac in H6. exists a. exists F!f. assumption. }
    assert (SFL.Functional g) as H7. {
      intros x y z H7 H8. rewrite H5 in H7. rewrite H5 in H8.
      apply Union2.Charac in H7. apply Union2.Charac in H8.
      destruct H7 as [H7|H7]; destruct H8 as [H8|H8].
      - apply H3 with x; assumption.
      - exfalso. apply Single.Charac in H8. apply OrdPair.WhenEqual in H8.
        destruct H8 as [H8 _]. subst.
        assert (a :< domain f) as H9. { apply SRD.Charac. exists y. assumption. }
        rewrite G1 in H9. apply (SOI.IsLess R A A) in H9; try assumption.
        apply (WellFoundedWellOrd.IsIrreflexive R A H1 a); assumption.
      - exfalso. apply Single.Charac in H7. apply OrdPair.WhenEqual in H7.
        destruct H7 as [H7 _]. subst.
        assert (a :< domain f) as H9. { apply SRD.Charac. exists z. assumption. }
        rewrite G1 in H9. apply (SOI.IsLess R A A) in H9; try assumption.
        apply (WellFoundedWellOrd.IsIrreflexive R A H1 a); assumption.
      - apply Single.Charac in H7. apply Single.Charac in H8.
        apply OrdPair.WhenEqual in H7. apply OrdPair.WhenEqual in H8.
        destruct H7 as [_ H7]. destruct H8 as [_ H8]. subst. reflexivity. }
    assert (SRF.Function g) as H8. { split; assumption. }
    assert (domain g = initSegment R^:=: A a) as H9. {
      apply SIN.DoubleInclusion. split; intros x H9.
      - apply SRD.Charac in H9. destruct H9 as [y H9].
        rewrite H5 in H9. apply Union2.Charac in H9. destruct H9 as [H9|H9].
        + apply (SOI.InitRefl R A A); try assumption. right. rewrite <- G1.
          apply SRD.Charac. exists y. assumption.
        + apply Single.Charac in H9.
          apply OrdPair.WhenEqual in H9. destruct H9 as [H9 H10].
          apply (SOI.InitRefl R A A); try assumption. left. split; assumption.
      - apply (SOI.InitRefl R A A) in H9; try assumption.
        apply SRD.Charac. destruct H9 as [H9|H9].
        + destruct H9 as [H9 H10]. exists F!f. rewrite H5. apply Union2.Charac.
          right. apply Single.Charac. subst. reflexivity.
        + rewrite <- G1 in H9. apply SRD.Charac in H9. destruct H9 as [y H9].
          exists y. rewrite H5. apply Union2.Charac. left. assumption. }
    split; assumption. }
  assert (g:|:initSegment R A a = f) as G5. {
    assert (SFO.FunctionOn (g:|:initSegment R A a) (initSegment R A a)) as H6. {
      apply SFO.Restrict with (initSegment R^:=: A a). 1: assumption.
      apply (SOI.IsInclRefl R A A); assumption. }
    apply SFO.EqualCharac with (initSegment R A a) (initSegment R A a);
    try assumption. 1: reflexivity.
    intros x H7.
    assert ((g:|:initSegment R A a)!x = g!x) as H8. {
      apply Restrict.Eval. 2: assumption. apply G4. }
    rewrite H8. apply SRF.EvalCharac.
    - apply G4.
    - assert (domain g = initSegment R^:=: A a) as H9. { apply G4. }
      rewrite H9. apply (SOI.InitRefl R A A); try assumption.
      right. assumption.
    - rewrite H5. apply Union2.Charac. left.
      apply SFO.Satisfies with (initSegment R A a); assumption. }
  assert (Transitive R A) as G6. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  split. 1: assumption.
  intros b H6. apply (SOI.InitRefl R A A) in H6; try assumption.
  destruct H6 as [H6|H6].
  - destruct H6 as [H6 H7].
    assert (g!b = F!f) as H8. {
      rewrite H7. apply (SFO.EvalCharac g (initSegment R^:=: A a)). 1: assumption.
      - apply (SOI.IsInRefl R A A); assumption.
      - rewrite H5. apply Union2.Charac. right. apply Single.Charac. reflexivity. }
    rewrite H8, H7, G5. reflexivity.
  - assert (g!b = f!b) as H8. {
      apply (SFO.EvalCharac g (initSegment R^:=: A a)). 1: assumption.
      - apply (SOI.InitRefl R A A); try assumption. right. assumption.
      - rewrite H5. apply Union2.Charac. left.
        apply SFO.Satisfies with (initSegment R A a); assumption. }
        assert (f:|:initSegment R A b = g:|:initSegment R A b) as H9. {
          rewrite <- G5. apply Restrict.TowerProperty.
          apply (SOI.WhenLess R A A); try assumption.
          - apply (SOI.IsIn R A A) with a; try assumption.
          - apply (SOI.IsLess R A A); assumption. }
        rewrite H8, <- H9. apply H4. assumption.
Qed.

(* The recursion class associated with R A F has domain A.                      *)
Proposition DomainIsA : forall (R A F:Class),
  WellFoundedWellOrd R A              ->
  HasNoMaximal R A                    ->
  CRD.domain (Recursion R A F) :~: A.
Proof.
  intros R A F H1 H2.
  remember (CRD.domain (Recursion R A F)) as B eqn:H3.
  assert (WellFounded R A) as H4. { apply H1. }
  assert (Transitive R A) as G1. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (A :<=: A) as H5. { apply Class.Incl.Refl. }
  assert (B :<=: A) as H6. {
    rewrite H3. intros x [y H6]. destruct H6 as [f [a [H6 [H7 [[_ H8] _]]]]].
    assert (x :< domain f) as H9. {
      apply SRD.Charac. exists y. assumption. }
    rewrite H8 in H9. apply SOI.IsIn with R A a; assumption. }
  assert (forall a, A a -> B a) as H7. {
    apply Induction' with R. 1: assumption.
    intros c H7 H8.
    remember (Recursion R A F :|: initSegment R A c) as f eqn:H9.
    assert (K R A F f c) as H10. {
      apply Restrict_; try assumption.
      intros b H10. rewrite <- H3. apply H8.
      apply (SOI.ToClass R A A) in H10; assumption. }
    remember (f :\/: :{ :(c,F!f): }:) as g eqn:H11.
    assert (KExt R A F g c) as H12. { apply Extend with f; assumption. }
    assert (~ Maximal R A c) as H13. {
      intros H13. apply H2. exists c. assumption. }
    assert (K R A F g (succ R A c)) as H14. {
      destruct H12 as [H12 [H15 H16]].
      assert (initSegment R A (succ R A c) = initSegment R^:=: A c) as H17. {
        apply Succ.InitRefl; assumption. }
      rewrite <- H17 in H15. rewrite <- H17 in H16.
      assert (A (succ R A c)) as H18. { apply Succ.IsIn; assumption. }
      split. 1: assumption. split; assumption. }
    rewrite H3. exists g!c. apply Charac2. exists g. exists (succ R A c).
    split. 2: assumption. apply SFO.Satisfies with (initSegment R A (succ R A c)).
    1: apply H14. apply Succ.InInit; assumption. }
  apply CIN.DoubleInclusion. split; assumption.
Qed.

(* The recursion class associated with R A F is a function class defined on A.  *)
Proposition IsFunctionOn : forall (R A F:Class),
  WellFoundedWellOrd R A              ->
  HasNoMaximal R A                    ->
  CFO.FunctionOn (Recursion R A F) A.
Proof.
  intros R A F H1 H2. split.
  - apply IsFunction. assumption.
  - apply DomainIsA; assumption.
Qed.

Lemma RestrictIsFunctionOn : forall (R A F:Class) (a b:U),
  WellFoundedWellOrd R A                        ->
  HasNoMaximal R A                              ->
  A a                                           ->
  b = initSegment R A a                         ->
  SFO.FunctionOn ((Recursion R A F) :|: b) b.
Proof.
  intros R A F a b H1 H2 H3 H4.
  assert (WellFounded R A) as H5. { apply H1. }
  assert (A :<=: A) as H6. { apply Class.Incl.Refl. }
  split.
  - apply RestrictOfClass.IsFunction, IsFunction. assumption.
  - apply RestrictOfClass.DomainWhenIncl.
    + apply IsFunction. assumption.
    + apply Class.Incl.EquivCompatR with A.
      * apply Equiv.Sym, DomainIsA; assumption.
      * intros x H7. apply (SOI.IsIn R A A) with a; try assumption.
        rewrite H4 in H7. assumption.
Qed.

Lemma K_Restrict : forall (R A F:Class) (f a:U),
  WellFoundedWellOrd R A                          ->
  HasNoMaximal R A                                ->
  K R A F f a                                     ->
  f = (Recursion R A F) :|: (initSegment R A a).
Proof.
  intros R A F f a H1 H2 H3. assert (H4 := H3). destruct H4 as [H4 [H5 H6]].
  remember (initSegment R A a) as b eqn:H7.
  assert (WellFounded R A) as H8. { apply H1. }
  assert (A :<=: A) as H9. { apply Class.Incl.Refl. }
  apply SFO.EqualCharac with b b. 1: assumption.
  - apply RestrictIsFunctionOn with a; assumption.
  - reflexivity.
  - intros x H10.
    assert (((Recursion R A F) :|: b)!x = (Recursion R A F)!x) as H11. {
      apply RestrictOfClass.Eval. 2: assumption. apply IsFunction. assumption. }
    rewrite H11. symmetry. apply (CFO.EvalCharac (Recursion R A F) A).
    + apply IsFunctionOn; assumption.
    + apply (SOI.IsIn R A A a); try assumption. rewrite <- H7. assumption.
    + apply Charac2. exists f. exists a. split. 2: assumption.
      apply SFO.Satisfies with b; assumption.
Qed.

(* The recursion class associated with R A F is F-recursive.                    *)
Proposition IsRecursive : forall (R A F:Class) (b:U),
  WellFoundedWellOrd R A                                              ->
  HasNoMaximal R A                                                    ->
  A b                                                                 ->
  (Recursion R A F)!b = F!((Recursion R A F :|: initSegment R A b)).
Proof.
  intros R A F b H1 H2 H3.
  remember (initSegment R A b) as c eqn:H4.
  assert (WellFounded R A) as H5. { apply H1. }
  assert (A :<=: A) as H6. { apply Class.Incl.Refl. }
  assert (Transitive R A) as G1. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (Recursion R A F :(b,(Recursion R A F)!b):) as H7. {
    apply CFO.Satisfies with A. 2: assumption. apply IsFunctionOn; assumption. }
  apply (proj1 (Charac2 _ _ _ _ _)) in H7. destruct H7 as [f [a [H7 H8]]].
  assert (H9 := H8). destruct H9 as [H9 [H10 H11]].
  assert (b :< initSegment R A a) as H12. {
    destruct H10 as [_ H10]. rewrite <- H10. apply SRD.Charac.
    exists (Recursion R A F)!b. assumption. }
  assert ((Recursion R A F)!b = f!b) as H13. {
    symmetry. apply (SFO.EvalCharac f (initSegment R A a)); assumption. }
  assert (f = (Recursion R A F) :|: (initSegment R A a)) as H14. {
    apply K_Restrict; assumption. }
  assert (f:|:c = (Recursion R A F) :|: c) as H15. {
    rewrite H14. apply RestrictOfClass.TowerProperty.
    - apply IsFunction; assumption.
    - rewrite H4. apply (SOI.WhenLess R A A); try assumption.
      apply (SOI.IsLess R A A); assumption. }
  rewrite H13, <- H15, H4. apply H11. assumption.
Qed.

(* The recursion class of R A F is the unique F-recursive funcrion on A.        *)
Proposition IsUnique : forall (R A F G:Class),
  WellFoundedWellOrd R A                               ->
  HasNoMaximal R A                                     ->
  CFO.FunctionOn G A                                   ->
  (forall b, A b -> G!b = F!(G:|:initSegment R A b))   ->
  G :~: Recursion R A F.
Proof.
  intros R A F G H1 H2 H3 H4.
  assert (WellFounded R A) as H5. { apply H1. }
  assert (A :<=: A) as H6. { apply Class.Incl.Refl. }
  apply (CFO.EqualCharac _ _ A A). 1: assumption.
  - apply IsFunctionOn; assumption.
  - split. 1: apply Equiv.Refl. apply Induction' with R. 1: assumption.
    intros a H7 H8.
    remember (initSegment R A a) as b eqn:H9.
    assert (SRD.domain (G:|:b) = b) as H10. {
      apply RestrictOfClass.DomainWhenIncl. 1: apply H3. destruct H3 as [_ H3].
      intros x H10. apply H3. rewrite H9 in H10.
      apply (SOI.IsIn R A A a); assumption. }
    assert (SRD.domain ((Recursion R A F) :|: b) = b) as H11. {
      apply RestrictOfClass.DomainWhenIncl.
      - apply IsFunction. assumption.
      - intros x H11. apply DomainIsA; try assumption.
        rewrite H9 in H11. apply (SOI.IsIn R A A a); assumption. }
    assert (G:|:b = (Recursion R A F) :|: b) as H12. {
      apply SRF.EqualCharac.
      - apply RestrictOfClass.IsFunction, H3.
      - apply RestrictOfClass.IsFunction, IsFunction. assumption.
      - rewrite H10, H11. reflexivity.
      - intros x H12. rewrite H10 in H12.
        assert ((G:|:b)!x = G!x) as H13. {
          apply RestrictOfClass.Eval. 2: assumption. apply H3. }
        assert (((Recursion R A F) :|: b)!x = (Recursion R A F)!x) as H14. {
          apply RestrictOfClass.Eval. 2: assumption.
          apply IsFunction. assumption. }
        rewrite H13, H14. apply H8. apply (SOI.ToClass R A A); try assumption.
        rewrite H9 in H12. assumption. }
        assert (G!a = F!(G:|:b)) as H15. { rewrite H9. apply H4. assumption. }
        assert ((Recursion R A F)!a = F!((Recursion R A F) :|: b)) as H16. {
          rewrite H9. apply IsRecursive; assumption. }
        rewrite H15, H16, H12. reflexivity.
Qed.

Proposition DomainWhenMax : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A                                    ->
  Maximal R A a                                             ->
  CRD.domain (Recursion R A F) :~: COI.initSegment R A a.
Proof.
  intros R A F a H1 H2.
  remember (CRD.domain (Recursion R A F)) as B eqn:H3.
  remember (COI.initSegment R A a) as C eqn:H4.
  assert (WellFounded R A) as H5. { apply H1. }
  assert (Transitive R A) as H6. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (A :<=: A) as H7. { apply Class.Incl.Refl. }
  assert (A a) as H8. { apply Maximal.IsIn with R. assumption. }
  assert (forall x, A x -> R^:=: :(x,a):) as H9. {
    intros x H9. apply ReflClosure.Charac2.
    assert (x = a \/ R :(x,a): \/ R :(a,x):) as H10. { apply H1; assumption. }
    destruct H10 as [H10|[H10|H10]].
    - left. assumption.
    - right. assumption.
    - exfalso. destruct H2 as [_ H2]. apply (H2 x); assumption. }
  assert (B :<=: C) as H10. {
    rewrite H3. intros x [y H10]. destruct H10 as [f [b [H10 [H11 [[_ H12] _]]]]].
    assert (x :< domain f) as H13. {
      apply SRD.Charac. exists y. assumption. }
    assert (R^:=: :(b,a):) as H14. { apply H9. assumption. }
    rewrite H12 in H13. rewrite H4. apply (SOI.ToClass R A A); try assumption.
    apply (SOI.WhenLeq R A A b); assumption. }
  assert (C :<=: A) as H11. {
    rewrite H4. apply COI.IsIncl. }
  assert (WellFoundedWellOrd R C) as H12. {
    apply WellFoundedWellOrd.WhenIncl with A; assumption. }
  assert (forall b, C b -> B b) as H13. {
    apply Induction' with R. 1: assumption.
    intros c H13 H14.
    remember (Recursion R A F :|: initSegment R A c) as f eqn:H15.
    assert (A c) as H16. { apply H11. assumption. }
    assert (R :(c,a):) as H17. {
      apply (SOI.IsLess R A A); try assumption.
      apply (SOI.ToClass R A A); try assumption. rewrite <- H4. assumption. }
    assert (initSegment R A c = initSegment R C c) as H18. {
      apply ZF.Set.Incl.DoubleInclusion. split; intros x H18.
      - apply (SOI.Charac R A A) in H18; try assumption. destruct H18 as [H18 H19].
        apply (SOI.CharacRev R A C); try assumption. rewrite H4.
        apply COI.Charac. split. 1: assumption. apply H6 with c; assumption.
      - apply (SOI.Charac R A C) in H18; try assumption. destruct H18 as [H18 H19].
        apply (SOI.CharacRev R A A); try assumption.
        apply COI.IsIn with R a. rewrite <- H4. assumption. }
    assert (K R A F f c) as H19. {
      apply Restrict_; try assumption.
      intros b H19. rewrite <- H3. apply H14.
      apply (SOI.ToClass R A C); try assumption. rewrite <- H18. assumption. }
    remember (f :\/: :{ :(c,F!f): }:) as g eqn:H20.
    assert (KExt R A F g c) as H21. { apply Extend with f; assumption. }
    assert (~Maximal R A c) as H22. {
      intros [H22 H23]. apply (H23 a); assumption. }
    assert (K R A F g (succ R A c)) as H23. {
      destruct H21 as [H21 [H23 H24]].
      assert (initSegment R A (succ R A c) = initSegment R^:=: A c) as H25. {
        apply Succ.InitRefl; assumption. }
      rewrite <- H25 in H23. rewrite <- H25 in H24.
      assert (A (succ R A c)) as H26. { apply Succ.IsIn; assumption. }
      split. 1: assumption. split; assumption. }
    rewrite H3. exists g!c. apply Charac2. exists g. exists (succ R A c).
    split. 2: assumption. apply SFO.Satisfies with (initSegment R A (succ R A c)).
    1: apply H23. apply Succ.InInit; assumption. }
  apply CIN.DoubleInclusion. split; assumption.
Qed.

Proposition IsSmall : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A    ->
  Maximal R A a             ->
  Small (Recursion R A F).
Proof.
  intros R A F a H1 H2. apply CRF.IsSmall.
  - apply IsFunction. assumption.
  - apply Small.EquivCompat with (COI.initSegment R A a).
    + apply Equiv.Sym, DomainWhenMax; assumption.
    + apply H1, Maximal.IsIn with R. assumption.
Qed.

Proposition IsFunctionOnWhenMax : forall (R A F:Class) (a:U),
  WellFoundedWellOrd R A                                    ->
  Maximal R A a                                             ->
  CFO.FunctionOn (Recursion R A F) (COI.initSegment R A a).
Proof.
  intros R A F a H1 H2. split.
  - apply IsFunction. assumption.
  - apply DomainWhenMax; assumption.
Qed.

Proposition Restrict : forall (R A F:Class) (a f:U),
  WellFoundedWellOrd R A                                                ->
  A a                                                                   ->
  f = (Recursion R A F) :|: initSegment R A a                           ->
  K R A F f a.
Proof.
  intros R A F a f H1 H2 H3. apply Restrict_; try assumption. intros b H4.
  assert (WellFounded R A) as G1. { apply H1. }
  assert (A :<=: A) as G2. { apply Class.Incl.Refl. }
  assert (Total R A) as G3. { apply H1. }
  assert (Transitive R A) as G4. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (HasNoMaximal R A \/ ~ HasNoMaximal R A) as H5. {
    apply LawExcludedMiddle. }
  assert (A b) as H6. { apply (InitSegment.IsIn R A A a); assumption. }
  destruct H5 as [H5|H5].
  - apply DomainIsA; assumption.
  - apply DoubleNegation in H5. destruct H5 as [c H5].
    apply (DomainWhenMax R A F c); try assumption.
    apply COI.Charac. split. 1: assumption.
    apply (ReflClosure.LessLeqTran R A) with a; try assumption.
    + apply Maximal.IsIn with R. assumption.
    + apply (InitSegment.IsLess R A A); assumption.
    + apply (ReflClosure.WhenMax R A c) in H2; try assumption.
      apply COI.IsLess with A. assumption.
Qed.
