Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Specify.

Module COC := ZF.Class.Ordinal.Core.
Module CRF := ZF.Class.Relation.Function.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRO := ZF.Class.Relation.OneToOne.
Module SOC := ZF.Set.Ordinal.Core.
Module SRF := ZF.Class.Relation.Function.
Module SFO := ZF.Set.Relation.FunctionOn.
Module SRO := ZF.Set.Relation.OneToOne.

Proposition WhenFreshValue : forall (F A:Class),
  CFO.FunctionOn F On                             ->
  (forall a, On a -> (A :\: toClass F:[a]:) F!a)  ->
  range F :<=: A                                  /\
  CRO.OneToOne F                                  /\
  Proper A.
Proof.
  intros F A H1 H2.
  assert (range F :<=: A) as H3. {
    intros b H3. apply (CFO.RangeCharac F On) in H3. 2: assumption.
    destruct H3 as [a [H3 H4]]. subst. apply H2. assumption. }
  assert (CRO.OneToOne F) as H4. {
    apply CFO.IsOneToOne with On. 1: assumption.
    intros a b H4 H5 H6.
    assert (a = b \/ a :< b \/ b :< a) as H7. {
      apply SOC.OrdinalTotal; assumption. }
    destruct H7 as [H7|[H7|H7]]. 1: assumption.
    - exfalso. specialize (H2 b H5). rewrite <- H6 in H2.
      destruct H2 as [_ H2]. apply H2.
      apply ImageByClass.IsIn; try apply H1; assumption.
    - exfalso. specialize (H2 a H4). rewrite H6 in H2.
      destruct H2 as [_ H2]. apply H2.
      apply ImageByClass.IsIn; try apply H1; assumption. }
  assert (Proper A) as H5. {
    intros H5.
    assert (Small (range F)) as H6. {
      apply Bounded.WhenSmaller with A; assumption. }
    assert (Small On) as H7. {
      apply Small.EquivCompat with (domain F). 1: apply H1.
      apply CRF.DomainIsSmall; assumption. }
    revert H7. apply COC.OnIsProper. }
  split. 1: assumption. split; assumption.
Qed.

Proposition WhenFreshAndSmall : forall (F A:Class),
  CFO.FunctionOn F On                                                     ->
  Small A                                                                 ->
  (forall a,
    On a                            ->
    (A :\: toClass F:[a]:) :<>: :0: ->
    (A :\: toClass F:[a]:) F!a                                          ) ->

  exists a,
    On a                                                                  /\
    (forall b, b :< a -> (A :\: toClass F:[b]:) :<>: :0:)                 /\
    toClass F:[a]: :~: A                                                  /\
    SRO.OneToOne (F :|: a).
Proof.
  intros F A H1 H2 H3.
  assert (exists a, On a /\ A :\: toClass F:[a]: :~: :0:) as H4. {
    apply NotForAllNot. intros H4.
    assert (forall a, On a -> (A :\: toClass F:[a]:) F!a) as H5. {
      intros a H5. apply H3. 1: assumption.
      intros H6. apply H4 with a. split; assumption. }
    assert (Proper A) as H6. { apply (WhenFreshValue F A); assumption. }
    contradiction. }
  remember (fun a => On a /\  A :\: toClass F:[a]: :~: :0:) as B eqn:H5.
  assert (B :<>: :0:) as H6. { apply Class.Empty.HasElem. assumption. }
  assert (COC.Ordinal On) as H7. { apply COC.OnIsOrdinal. }
  assert (B :<=: On) as H8. { intros x H8. rewrite H5 in H8. apply H8. }
  assert (exists a, B a /\ B :/\: toClass a :~: :0:) as H9. {
    apply COC.HasEMinimal with On; assumption. }
  destruct H9 as [a [H9 H10]].
  assert (On a) as H11. { rewrite H5 in H9. apply H9. }
  assert (A :\: toClass F:[a]: :~: :0:) as H12. { rewrite H5 in H9. apply H9. }
  assert (forall b, b :< a -> (A :\: toClass F:[b]:) :<>: :0:) as H13. {
    intros b H13 H14.
    assert (On b) as H15. { apply SOC.IsOrdinal with a; assumption. }
    apply Class.Empty.Charac with b. apply H10. split. 2: assumption.
    rewrite H5. split; assumption. }
  assert (toClass F:[a]: :<=: A) as H14. {
    intros y H14. apply ImageByClass.Charac in H14. 2: apply H1.
    destruct H14 as [b [H14 H15]].
    assert (On b) as H16. { apply SOC.IsOrdinal with a; assumption. }
    assert (F!b = y) as H17. { apply (CFO.EvalCharac F On); assumption. }
    assert ((A :\: toClass F:[b]:) :<>: :0:) as H18. { apply H13. assumption. }
    assert ((A :\: toClass F:[b]:) F!b) as H19. { apply H3; assumption. }
    rewrite H17 in H19. apply H19. }
  assert (A :<=: toClass F:[a]:) as H15. { apply Diff.WhenEmpty. assumption. }
  assert (toClass F:[a]: :~: A) as H16. {
    apply DoubleInclusion. split; assumption. }
  assert (SFO.FunctionOn (F:|:a) a) as H17. {
    split.
    - apply RestrictOfClass.IsFunction, H1.
    - rewrite RestrictOfClass.DomainOf. 2: apply H1.
      apply Specify.IsA. intros b H17. apply H1.
      apply SOC.IsOrdinal with a; assumption. }
  assert (SRO.OneToOne (F:|:a)) as H18. {
    apply SFO.IsOneToOne with a. 1: assumption.
    intros b c H18 H19 H20.
    assert (On b) as H21. { apply SOC.IsOrdinal with a; assumption. }
    assert (On c) as H22. { apply SOC.IsOrdinal with a; assumption. }
    assert ((F:|:a)!b = F!b) as H23. {
      apply RestrictOfClass.Eval. 1: apply H1. assumption. }
    assert ((F:|:a)!c = F!c) as H24. {
      apply RestrictOfClass.Eval. 1: apply H1. assumption. }
    rewrite H23 in H20. rewrite H24 in H20.
    assert (b = c \/ b :< c \/ c :< b) as H25. {
      apply SOC.OrdinalTotal; assumption. }
    destruct H25 as [H25|[H25|H25]]. 1: assumption.
    - exfalso. specialize (H13 c H19). specialize (H3 c H22 H13).
      rewrite <- H20 in H3. destruct H3 as [_ H3]. apply H3.
      apply ImageByClass.IsIn; try apply H1; assumption.
    - exfalso. specialize (H13 b H18). specialize (H3 b H21 H13).
      rewrite H20 in H3. destruct H3 as [_ H3]. apply H3.
      apply ImageByClass.IsIn; try apply H1; assumption. }
  exists a. split. 1: assumption. split. 1: assumption. split; assumption.
Qed.
