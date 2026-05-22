Require Import ZF.Axiom.Classic.
Require Import ZF.Class.DiffBySet.
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
Require Import ZF.Class.Ordinal.MinFresh.
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
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CMF := ZF.Class.Ordinal.MinFresh.
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

(* The canonical isomorphism from On onto A, from recursion over MinFresh.      *)
Definition Enum (R A:Class) : Class := Recursion (CMF.MinFresh R A).

(* MinFresh picks the R-minimal element of A not in the range of its argument.  *)
Definition MinFresh (R A:Class) : Class := CMF.MinFresh R A.

(* G is MinFresh-recursive for R A: each G(a) is the next fresh minimum.        *)
Definition Recursive (R A G:Class) : Prop :=
  forall a, On a -> G!a = (MinFresh R A)!(G:|:a).

(* If G is recursive, G(a) is R-minimal in the difference A\G[a].               *)
Proposition IsMinimal : forall (R A G:Class) (a:U),
  WellFoundedWellOrd R A          ->
  CFO.FunctionOn G On             ->
  Recursive R A G                 ->
  On a                            ->
  (A :\: G:[a]:) :<>: :0:         ->
  Minimal R (A :\: G:[a]:) G!a.
Proof.
  (* Proof by Claude. *)
  intros R A G a H1 H2 H3 H4 H5.
  assert (SRR.range (G:|:a) = G:[a]:) as H6. {
    apply RestrictOfClass.RangeOf, H2. }
  rewrite (H3 a H4).
  rewrite <- H6.
  apply CMF.IsMinimal; try assumption. rewrite H6. assumption.
Qed.

(* A recursive function class defined on On is an isomorphism from On to A.     *)
Proposition IsIsom' : forall (R A G:Class),
  WellFoundedWellOrd R A          ->
  Proper A                        ->
  CFO.FunctionOn G On             ->
  Recursive R A G                 ->
  Isom G E R On A.
Proof.
  (* Proof by Claude. *)
  intros R A G H1 H2 H3 H4.
  assert (forall a, On a -> (A :\: G:[a]:) :<>: :0:) as H6. {
    intros a H6. apply Proper.IsNotEmpty, DiffBySet.IsProper. assumption. }
  assert (forall a, On a -> Minimal R (A :\: G:[a]:) G!a) as H7. {
    intros a H7. apply IsMinimal; try assumption.
    apply H6. assumption. }
  assert (forall a, On a -> (A :\: G:[a]:) G!a) as H8. {
    intros a H8. apply Minimal.IsIn with R, H7. assumption. }
  assert (CRR.range G :<=: A) as H9. { apply WhenFreshValue; assumption. }
  assert (CRO.OneToOne G) as H10. { apply (WhenFreshValue G A); assumption. }
  assert (Proper (CRR.range G)) as H11. {
    intros H11.
    assert (Small On) as H12. {
      apply CFO.DomainIsSmall with G; assumption. }
    revert H12. apply COC.IsProper. }
  assert ( A :~: CRR.range G
    \/ exists a, A a /\ CRR.range G :~: initSegment R A a) as H12. {
    apply WellFoundedWellOrd.IsAllOrInitSegment; try assumption.
    intros x y H12 H13 H14.
    assert (exists a, On a /\ G!a = y) as H15. {
      apply CFO.RangeCharac; assumption. }
    destruct H15 as [a [H15 H16]].
    assert (Minimal R (A :\: G:[a]:) G!a) as H17. {
      apply IsMinimal; try assumption.
      apply Proper.IsNotEmpty, DiffBySet.IsProper. assumption. }
    destruct H17 as [H17 H18].
    assert (~ (A :\: G:[a]:) x) as H19. {
      intros H19. revert H14. rewrite <- H16. apply H18. assumption. }
    assert (x :< G:[a]:) as H20. {
      apply DoubleNegation. intros H20. apply H19. split; assumption. }
      apply ImageUnderClass.ToClass in H20. 2: apply H3.
      destruct H20 as [u [H20 H21]]. exists u. assumption. }
  assert (A :~: CRR.range G) as H13. {
    destruct H12 as [H12|H12]. 1: assumption. destruct H12 as [a [H12 H13]].
    exfalso. apply H11. apply Small.EquivCompat with (initSegment R A a).
    - apply Equiv.Sym. assumption.
    - apply H1. assumption. }
  assert (Bij G On A) as H14. {
    split.
    - split. 2: apply H3. split. 2: assumption. apply H3.
    - apply Equiv.Sym. assumption. }
  assert (forall a, On a -> A G!a) as G1. {
    intros a G1. apply H9. exists a. apply CFO.Satisfies with On; assumption. }
  assert (forall a b, On a -> On b -> a :< b -> R :(G!a,G!b):) as H15. {
    intros a b H15 H16 H17.
    assert (A G!a) as G2. { apply G1. assumption. }
    assert (A G!b) as G3. { apply G1. assumption. }
    assert (G:[a]: :<=: G:[b]:) as H18. {
      apply ImageUnderClass.InclCompatR. 1: apply H3.
      apply SOC.ElemIsIncl; assumption. }
    assert (A :\: G:[b]: :<=: A :\: G:[a]:) as H19. {
      apply DiffBySet.InclCompatR. assumption. }
    assert ((A :\: G:[a]:) G!b) as H20. {
      apply H19. apply Minimal.IsIn with R. apply H7. assumption. }
    assert (G!a = G!b \/ R :(G!a,G!b):) as H21. {
      apply Minimal.WhenIn with A (A :\: G:[a]:). 4: assumption.
      - apply H1.
      - apply Class.Inter2.IsInclL.
      - apply H7. assumption. }
    destruct H21 as [H21|H21]. 2: assumption. exfalso.
    assert (a = b) as H22. { apply (Bij.EvalInjective G On A); assumption. }
    subst. revert H17. apply Foundation.NoLoop1. }
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

(* Enum R A is a function class defined on the class of ordinals.               *)
Proposition IsFunctionOn : forall (R A:Class),
  CFO.FunctionOn (Enum R A) On.
Proof.
  intros R A. apply Recursion.IsFunctionOn.
Qed.

(* Enum R A is MinFresh-recursive.                                              *)
Proposition IsRecursive : forall (R A:Class),
  Recursive R A (Enum R A).
Proof.
  (* Proof by Claude. *)
  intros R A a H1. apply Recursion.IsRecursive. assumption.
Qed.

(* Enum R A is an isomorphism from On to A.                                     *)
Proposition IsIsom : forall (R A:Class),
  WellFoundedWellOrd R A                ->
  Proper A                              ->
  Isom (Enum R A) E R On A.
Proof.
  (* Proof by Claude. *)
  intros R A H1 H2.
  apply IsIsom'; try assumption.
  - apply IsFunctionOn.
  - apply IsRecursive.
Qed.

(* Enum R A is the unique isomorphism from On to A.                             *)
Proposition IsUnique : forall (R A G:Class),
  WellFoundedWellOrd R A                ->
  Proper A                              ->
  Isom G E R On A                       ->
  G :~: Enum R A.
Proof.
  (* Proof by Claude. *)
  intros R A G H1 H2 H3.
  remember (Enum R A) as F eqn:H4.
  assert (Isom F E R On A) as H5. {
    rewrite H4. apply IsIsom; assumption. }
  assert (Isom F^:-1: R E A On) as H6. { apply Isom.Converse. assumption. }
  remember (F^:-1: :.: G) as H eqn:H7.
  assert (Isom H E E On On) as H8. {
    rewrite H7. apply Isom.Compose with R A; assumption. }
  assert (forall a, On a -> H!a = a) as H9. {
    apply Isom.IsId with On; try apply COC.IsOrdinal. assumption. }
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
  apply (Bij.Equal G F On A). 3: assumption.
  - apply H3.
  - apply H5.
Qed.

(* A well ordered small class is isomorphic to an ordinal.                      *)
Proposition WhenSmall : forall (R A:Class),
  Small A                               ->
  WellOrdering R A                      ->
  exists a, On a                        /\
    forall (g:U),
      g = (Enum R A :|: a)              ->
      Isom (toClass g) E R (toClass a) A.
Proof.
  (* Proof by Claude. *)
  intros R A H1 H2.
  assert (WellFoundedWellOrd R A) as H3. {
    split. 2: assumption. apply WellFounded.WhenSmall. 1: assumption. apply H2. }
  remember (Enum R A) as G eqn:H4.
  assert (FunctionOn G On) as H5. {
    rewrite H4. apply IsFunctionOn. }
  assert (Recursive R A G) as H7. {
    rewrite H4. apply IsRecursive. }
  assert (forall a,
    On a                                  ->
    (A :\: G:[a]:) :<>: :0:       ->
    Minimal R (A :\: G:[a]:) G!a) as H8. {
      intros a H8 H9. apply IsMinimal; assumption. }
  assert (forall a,
    On a                                  ->
    (A :\: G:[a]:) :<>: :0:       ->
    (A :\: G:[a]:) G!a) as H9. {
      intros a H9 H10. apply Minimal.IsIn with R. apply H8; assumption. }
  assert (exists a,
    On a                                                                  /\
    (forall b, b :< a -> (A :\: G:[b]:) :<>: :0:)                 /\
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
      apply ImageUnderClass.InclCompatR. 2: assumption. apply H5. }
    assert ((A :\: G:[c]:) :<=: (A :\: G:[b]:)) as H34. {
      apply DiffBySet.InclCompatR. assumption. }
    assert ((A :\: G:[c]:) G!c) as H35. {
      apply H9. 1: assumption. apply H11. assumption. }
    assert ((A :\: G:[b]:) G!c) as H36. { apply H34. assumption. }
    assert (G!b = G!c \/ R :(G!b,G!c):) as H37. {
      apply Minimal.WhenIn with A (A :\: G:[b]:). 4: assumption.
      - apply H2.
      - apply Class.Inter2.IsInclL.
      - apply H8. 1: assumption. apply H11. assumption. }
    destruct H37 as [H37|H37]. 2: { rewrite H28, H29. assumption. } exfalso.
    assert (b = c) as H38. {
      apply SBO.EvalInjective with g a; try assumption.
      rewrite H28, H29. assumption. }
    revert H25. rewrite H38. apply Foundation.NoLoop1. }
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

(* The ordinal and isomorphism for a small well-ordering are unique.            *)
Proposition WhenSmallUnique : forall (R A:Class) (a b f g:U),
  Small A                               ->
  WellOrdering R A                      ->
  On a                                  ->
  On b                                  ->
  Isom (toClass f) E R (toClass a) A    ->
  Isom (toClass g) E R (toClass b) A    ->
  a = b /\ f = g.
Proof.
  (* Proof by Claude. *)
  intros R A a b f g H1 H2 H3 H4 H5 H6.
  assert (toClass a :~: toClass b /\ toClass f :~: toClass g) as H7. {
    apply Isom.IsEquivGen with R A; assumption. }
  split; apply Equiv.EqualToClass, H7.
Qed.
