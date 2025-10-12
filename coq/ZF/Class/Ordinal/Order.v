Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.FunctionOn.
Require Import ZF.Class.Ordinal.Isom.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.BijectionOn.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CIN := ZF.Class.Incl.
Module COC := ZF.Class.Ordinal.Core.
Module COF := ZF.Class.Ordinal.FunctionOn.
Module CRB := ZF.Class.Relation.Bijection.
Module CBO := ZF.Class.Relation.BijectionOn.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRO := ZF.Class.Relation.OneToOne.
Module CRR := ZF.Class.Relation.Range.

Module SIN := ZF.Set.Incl.
Module SOC := ZF.Set.Ordinal.Core.
Module SRB := ZF.Set.Relation.Bijection.
Module SBO := ZF.Set.Relation.BijectionOn.
Module SRD := ZF.Set.Relation.Domain.
Module SRF := ZF.Set.Relation.Function.
Module SRO := ZF.Set.Relation.OneToOne.
Module SRR := ZF.Set.Relation.Range.

(* With appropriate assumptions, this is the function class which given a       *)
(* function y, selects the smallest 'fresh' value z of A, i.e. the smallest     *)
(* element z of A which has not yet been 'used' by y.                           *)
Definition SmallestFresh (R A:Class) : Class := fun x =>
  exists y z, x = :(y,z): /\ Minimal R (A :\: toClass (SRR.range y)) z.

(* With appropriate assumptions, the isomorphism between On and A.              *)
Definition RecurseSmallestFresh (R A:Class) : Class
  := Recursion (SmallestFresh R A).

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

Lemma WhenRecurseSmallestFresh_ : forall (R A F G:Class),
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

Lemma WhenRecurseSmallestFresh : forall (R A F G:Class),
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
    intros a H7. apply WhenRecurseSmallestFresh_ with F; try assumption.
    apply H6. assumption. }
  assert (forall a, On a -> (A :\: toClass G:[a]:) G!a) as H8. {
    intros a H8. apply Minimal.IsIn with R, H7. assumption. }
  assert (CRR.range G :<=: A) as H9. { apply WhenFreshValue; assumption. }
  assert (CRO.OneToOne G) as H10. { apply (WhenFreshValue G A); assumption. }
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
      apply WhenRecurseSmallestFresh_ with F; try assumption.
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
  assert (forall a, On a -> A G!a) as G1. {
    intros a G1. apply H9. exists a. apply CFO.Satisfies with On; assumption. }
  assert (forall a b, On a -> On b -> a :< b -> R :(G!a,G!b):) as H15. {
    intros a b H15 H16 H17.
    assert (A G!a) as G2. { apply G1. assumption. }
    assert (A G!b) as G3. { apply G1. assumption. }
    assert (G:[a]: :<=: G:[b]:) as H18. {
      apply ImageByClass.InclCompatR. 1: apply H4.
      apply SOC.ElemIsIncl; assumption. }
    assert (A :\: toClass G:[b]: :<=: A :\: toClass G:[a]:) as H19. {
      apply Class.Diff.InclCompatR. assumption. }
    assert ((A :\: toClass G:[a]:) G!b) as H20. {
      apply H19. apply Minimal.IsIn with R. apply H7. assumption. }
    assert (G!a = G!b \/ R :(G!a,G!b):) as H21. {
      apply Minimal.WhenIn with A (A :\: toClass G:[a]:). 4: assumption.
      - apply H1.
      - apply Class.Inter2.IsInclL.
      - apply H7. assumption. }
    destruct H21 as [H21|H21]. 2: assumption. exfalso.
    assert (a = b) as H22. { apply (Bij.EvalInjective G On A); assumption. }
    subst. revert H17. apply NoElemLoop1. }
  assert (Irreflexive R A) as H16. {
    apply WellFoundedWellOrd.IsIrreflexive. assumption. }
  assert (Transitive R A) as H17. {
    apply WellFoundedWellOrd.IsTransitive. assumption. }
  assert (forall a b, On a -> On b -> R :(G!a,G!b): -> a :< b) as H18. {
    intros a b H18 H19 H20.
    assert (A G!a) as G2. { apply G1. assumption. }
    assert (A G!b) as G3. { apply G1. assumption. }
    assert (a = b \/ a :< b \/ b :< a) as H21. {
      apply SOC.IsTotal; assumption. }
    destruct H21 as [H21|[H21|H21]]. 2: assumption.
    - exfalso. subst. revert H20. apply H16. apply G1. assumption.
    - exfalso.
      assert (R :(G!b,G!a):) as H22. { apply H15; assumption. }
      assert (R :(G!a,G!a):) as H23. { apply H17 with G!b; assumption. }
      revert H23. apply H16. assumption. }
  split. 1: assumption. intros a b H19 H20. split; intros H21.
  - apply E.Charac2 in H21. apply H15; assumption.
  - apply E.Charac2. apply H18; assumption.
Qed.

(* RecurseSmallestFresh is a function class defined on the class of ordinals.   *)
Proposition IsFunctionOn : forall (R A G:Class),
  G :~: RecurseSmallestFresh R A -> CFO.FunctionOn G On.
Proof.
  intros R A G H1. apply CFO.EquivCompatL with (RecurseSmallestFresh R A).
  - apply Equiv.Sym. assumption.
  - apply Recursion.IsFunctionOn.
Qed.

(* RecurseSmallestFresh is SmallestFresh-recursive.                             *)
Proposition IsRecursive : forall (R A F G:Class),
  F :~: SmallestFresh R A             ->
  G :~: RecurseSmallestFresh R A      ->
  forall a, On a -> G!a = F!(G:|:a).
Proof.
  intros R A F G H1 H2 a H3.
  assert (G!a = (RecurseSmallestFresh R A)!a) as H4. {
    apply EvalOfClass.EquivCompat. assumption. }
  assert (G:|:a = (RecurseSmallestFresh R A) :|: a) as H5. {
    apply RestrictOfClass.EquivCompat. assumption. }
  assert (F!(G:|:a) = (SmallestFresh R A)!(G:|:a)) as H6. {
    apply EvalOfClass.EquivCompat. assumption. }
  rewrite H6, H5, H4. apply Recursion.IsRecursive. assumption.
Qed.

(* RecurseSmallestFresh is an isomorphism from On to A.                         *)
Proposition IsIsom : forall (R A G:Class),
  WellFoundedWellOrd R A                    ->
  Proper A                                  ->
  G :~: RecurseSmallestFresh R A            ->
  Isom G E R On A.
Proof.
  intros R A G H1 H2 H3.
  apply WhenRecurseSmallestFresh with (SmallestFresh R A); try assumption.
  - apply Equiv.Refl.
  - apply IsFunctionOn with R A. assumption.
  - apply IsRecursive with R A. 2: assumption. apply Equiv.Refl.
Qed.

(* RecurseSmallestFresh is the unique isomorphism from On to A.                 *)
Proposition IsUnique : forall (R A G:Class),
  WellFoundedWellOrd R A          ->
  Proper A                        ->
  Isom G E R On A                 ->
  G :~: RecurseSmallestFresh R A.
Proof.
  intros R A G H1 H2 H3.
  remember (RecurseSmallestFresh R A) as F eqn:H4.
  assert (Isom F E R On A) as H5. {
    apply IsIsom; try assumption. rewrite H4. apply Equiv.Refl. }
  assert (Isom F^:-1: R E A On) as H6. { apply Isom.Converse. assumption. }
  remember (F^:-1: :.: G) as H eqn:H7.
  assert (Isom H E E On On) as H8. {
    rewrite H7. apply Isom.Compose with R A; assumption. }
  assert (forall a, On a -> H!a = a) as H9. {
    apply Isom.IsId with On; try apply COC.OnIsOrdinal. assumption. }
  assert (forall a, On a -> G!a = F!a) as H10. {
    intros a H10.
    assert (F!(H!a) = G!a) as H11. {
      rewrite H7. rewrite (Bij.ComposeEval _ _ On A On); try assumption.
      - rewrite (Bij.EvalOfConverseEval F On A). 1: reflexivity.
        + apply H5.
        + apply H3. exists a. apply (Bij.Satisfies _ On A). 2: assumption.
          apply H3.
      - apply H3.
      - apply H6. }
    rewrite H9 in H11. 2: assumption. symmetry. assumption. }
  apply (Bij.EqualCharac' G F On A). 3: assumption.
  - apply H3.
  - apply H5.
Qed.

(* A well ordered small class is isomorphic to an ordinal.                      *)
Proposition WhenSmall : forall (R A:Class),
  Small A           ->
  WellOrdering R A  ->

  exists a, On a    /\
    forall (g:U),
      g = (RecurseSmallestFresh R A :|: a) ->
      Isom (toClass g) E R (toClass a) A.
Proof.
  intros R A H1 H2.
  assert (WellFoundedWellOrd R A) as H3. {
    split. 2: assumption. apply WellFounded.WhenSmall. 1: assumption. apply H2. }
  remember (RecurseSmallestFresh R A) as G eqn:H4.
  assert (G :~: RecurseSmallestFresh R A) as G1. {
    rewrite H4. apply Equiv.Refl. }
  assert (FunctionOn G On) as H5. {
    rewrite H4. apply IsFunctionOn with R A, Equiv.Refl. }
  remember (SmallestFresh R A) as F eqn: H6.
  assert (F :~: SmallestFresh R A) as G2. { rewrite H6. apply Equiv.Refl. }
  assert (forall a, On a -> G!a = F!(G:|:a)) as H7. {
    apply IsRecursive with R A; assumption. }
  assert (forall a,
    On a                                  ->
    (A :\: toClass G:[a]:) :<>: :0:       ->
    Minimal R (A :\: toClass G:[a]:) G!a) as H8. {
      apply WhenRecurseSmallestFresh_ with F; assumption. }
  assert (forall a,
    On a                                  ->
    (A :\: toClass G:[a]:) :<>: :0:       ->
    (A :\: toClass G:[a]:) G!a) as H9. {
      intros a H9 H10. apply Minimal.IsIn with R. apply H8; assumption. }
  assert (exists a,
    On a                                                                  /\
    (forall b, b :< a -> (A :\: toClass G:[b]:) :<>: :0:)                 /\
    toClass G:[a]: :~: A                                                  /\
    SRO.OneToOne (G :|: a)) as H10. { apply COF.WhenFreshAndSmall; assumption. }
  destruct H10 as [a [H10 [H11 [H12 H13]]]].
  exists a. split. 1: assumption. intros g H14.
  assert (domain g = a) as H15. {
    rewrite H14. apply RestrictOfClass.DomainWhenIncl. 1: apply H5.
    intros b H15. apply H5. apply SOC.IsOrdinal with a; assumption. }
  assert (SRF.Function g) as H16. {
    rewrite H14. apply RestrictOfClass.IsFunction. apply H5. }
  assert (SRB.Bijection g) as H17. {
    split. 1: apply H16. rewrite H14. assumption. }
  assert (SBO.BijectionOn g a) as H18. { split; assumption. }
  assert (CBO.BijectionOn (toClass g) (toClass a)) as H19. {
    apply SBO.ToClass. assumption. }
  assert (range g = G:[a]:) as H20. {
    rewrite H14. apply RestrictOfClass.RangeOf. apply H5. }
  assert (CRR.range (toClass g) :~: A) as H21. {
    apply Equiv.Tran with (toClass (SRR.range g)).
    - apply Equiv.Sym, SRR.ToClass.
    - rewrite H20. assumption. }
  assert (Bij (toClass g) (toClass a) A) as H22. { split; assumption. }
  assert (forall b c, b :< a -> c :< a -> b :< c -> R :(g!b,g!c):) as H23. {
    intros b c H23 H24 H25.
    assert (On b) as H26. { apply SOC.IsOrdinal with a; assumption. }
    assert (On c) as H27. { apply SOC.IsOrdinal with a; assumption. }
    assert (g!b = G!b) as H28. {
      rewrite H14. apply RestrictOfClass.Eval. 2: assumption. apply H5. }
    assert (g!c = G!c) as H29. {
      rewrite H14. apply RestrictOfClass.Eval. 2: assumption. apply H5. }
    assert (b :<=: c) as H30. { apply SOC.ElemIsIncl; assumption. }
    assert (b :<=: a) as H31. { apply SOC.ElemIsIncl; assumption. }
    assert (c :<=: a) as H32. { apply SOC.ElemIsIncl; assumption. }
    assert (G:[b]: :<=: G:[c]:) as H33. {
      apply ImageByClass.InclCompatR. 2: assumption. apply H5. }
    assert ((A :\: toClass G:[c]:) :<=: (A :\: toClass G:[b]:)) as H34. {
      apply Class.Diff.InclCompatR. assumption. }
    assert ((A :\: toClass G:[c]:) G!c) as H35. {
      apply H9. 1: assumption. apply H11. assumption. }
    assert ((A :\: toClass G:[b]:) G!c) as H36. { apply H34. assumption. }
    assert (G!b = G!c \/ R :(G!b,G!c):) as H37. {
      apply Minimal.WhenIn with A (A :\: toClass G:[b]:). 4: assumption.
      - apply H2.
      - apply Class.Inter2.IsInclL.
      - apply H8. 1: assumption. apply H11. assumption. }
    destruct H37 as [H37|H37]. 2: { rewrite H28, H29. assumption. } exfalso.
    assert (b = c) as H38. {
      apply SBO.EvalInjective with g a; try assumption.
      rewrite H28, H29. assumption. }
    revert H25. rewrite H38. apply NoElemLoop1. }
  assert (Irreflexive R A) as H24. {
    apply WellOrdering.IsIrreflexive. assumption. }
  assert (Transitive R A) as H25. {
    apply WellOrdering.IsTransitive. assumption. }
  assert (forall b, b :< a -> A g!b) as G3. {
    intros b G3. apply (Bij.IsInRange (toClass g) (toClass a) A); assumption. }
  assert (forall b c, b :< a -> c :< a -> R :(g!b,g!c): -> b :< c) as H26. {
    intros b c H26 H27 H28.
    assert (On b) as H29. { apply SOC.IsOrdinal with a; assumption. }
    assert (On c) as H30. { apply SOC.IsOrdinal with a; assumption. }
    assert (g!b = G!b) as H31. {
      rewrite H14. apply RestrictOfClass.Eval. 2: assumption. apply H5. }
    assert (g!c = G!c) as H32. {
      rewrite H14. apply RestrictOfClass.Eval. 2: assumption. apply H5. }
    assert (A g!b) as H33. { apply G3. assumption. }
    assert (A g!c) as H34. { apply G3. assumption. }
    assert (b = c \/ b :< c \/ c :< b) as H35. {
      apply SOC.IsTotal; assumption. }
    destruct H35 as [H35|[H35|H35]]. 2: assumption.
    - exfalso. rewrite H35 in H28. revert H28. apply H24. assumption.
    - assert (R :(g!c,g!b):) as H36. { apply H23; assumption. }
      assert (R :(g!b,g!b):) as H37. { apply H25 with g!c; assumption. }
      exfalso. revert H37. apply H24. assumption. }
  split. 1: assumption. intros b c H27 H28. split; intros H29.
  - apply E.Charac2 in H29. apply H23; assumption.
  - apply E.Charac2, H26; assumption.
Qed.
