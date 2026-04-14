Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.FunctionOn.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Class.Small.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module CEQ := ZF.Class.Equiv.
Module CFO := ZF.Class.Relation.FunctionOn.
Module COF := ZF.Class.Ordinal.FunctionOn.
Module CRD := ZF.Class.Relation.Domain.
Module CRO := ZF.Class.Relation.OneToOne.
Module CRR := ZF.Class.Relation.Range.
Module CRT := ZF.Class.Relation.ToFun.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SRI := ZF.Set.Relation.ImageByClass.

(* The cardinal of a set of the smallest ordinal in bijection with it.         *)
Definition card (a:U) : U := inf (fun b => Ordinal b /\ a :~: b).

(* The class of all cardinal numbers.                                          *)
Definition Cardinal : Class := fun b => exists a, b = card a.

Proposition HasOrdinal : Choice ->
  forall (a:U), exists b, Ordinal b /\ a :~: b.
Proof.
  intros AC a. specialize (AC :P(a)). destruct AC as [f [H1 H2]].
  remember (fun x => f!(a :\: range x)) as G eqn:H3.
  remember (Recursion (toFun G)) as F eqn:H4.
  assert (forall x,
    a :\: range x <> :0: -> f!(a :\: range x) :< a :\: range x) as H5. {
      intros x H5. apply H2. 2: assumption.
      apply Power.Charac, Diff.IsIncl. }
  assert (forall b, Ordinal b -> F!b = :[G]:!(F:|:b)) as H6. {
    intros b H6. rewrite H4. apply Recursion.IsRecursive. assumption. }
  assert (forall b , Ordinal b ->
    a :\: range (F:|:b) <> :0: -> F!b :< a :\: range (F:|:b)) as H7. {
      intros b H7 H8. rewrite H6, CRT.Eval, H3. 2: assumption.
      apply H5. assumption. }
  assert (CFO.FunctionOn F Ordinal) as G1. {
    rewrite H4. apply Recursion.IsFunctionOn. }
  assert (Small (toClass a)) as G2. { apply Small.SetIsSmall. }
  assert (CRD.domain F :~: Ordinal) as G3. { apply G1. }
  assert (forall b, Ordinal b               ->
    (toClass a :\: toClass F:[b]:) :<>: :0: ->
    (toClass a :\: toClass F:[b]:) F!b) as H8. {
      intros b H8 H9.
      assert (range (F:|:b) = F:[b]:) as H10. {
        apply RestrictOfClass.RangeOf, G1. }
      apply Diff.ToClass. rewrite <- H10. apply H7. 1: assumption.
      intros H11. apply H9.
      apply CEQ.Tran with (toClass (a :\: range (F:|:b))).
      - apply CEQ.Sym. rewrite <- H10. apply Diff.ToClass.
      - apply Empty.EmptyToClass. assumption. }
  assert (exists b,
    Ordinal b                                                     /\
    (forall c, c :< b -> (toClass a :\: toClass F:[c]:) :<>: :0:) /\
    toClass F:[b]: :~: toClass a                                  /\
    SRO.OneToOne (F:|:b)) as H9. { apply COF.WhenFreshAndSmall; assumption. }
  destruct H9 as [b [H9 [H10 [H11 H12]]]].
  assert (F:[b]: = a) as H13. { apply CEQ.EqualToClass. assumption. }
  assert (range (F:|:b) = a) as H14. {
    rewrite <- H13. apply RestrictOfClass.RangeOf, G1. }
  assert (domain (F:|:b) = b) as H15. {
    apply RestrictOfClass.DomainWhenIncl.
    - apply G1.
    - intros c H15. apply G3. apply Core.IsOrdinal with b; assumption. }
  assert (Bij (F:|:b) b a) as H16. {
    split. 2: assumption. split. 2: assumption. split. 2: assumption.
    apply RestrictOfClass.IsRelation, G1. }
  exists b. split. 1: assumption. apply Equiv.Sym. exists (F:|:b). assumption.
Qed.

Proposition IsOrdinal : forall (a:U), Ordinal (card a).
Proof.
  intros a. apply SOI.IsOrdinal.
Qed.

Proposition IsLowerBound : forall (a b:U),
  Ordinal b       ->
  a :~: b         ->
  card a :<=: b.
Proof.
  intros a b H1 H2. apply SOI.IsLowerBound.
  - intros c H3. apply H3.
  - split; assumption.
Qed.

Proposition IsLargest : forall (a b:U),
  Choice                                        ->
  Ordinal b                                     ->
  (forall c, Ordinal c -> a :~: c -> b :<=: c)  ->
  b :<=: card a.
Proof.
  intros a b AC H1 H2.
  apply SOI.IsLargest.
  - intros c H3. apply H3.
  - assert (exists c, Ordinal c /\ a :~: c) as H3. { apply HasOrdinal. assumption. }
    destruct H3 as [c H3]. apply CEM.HasElem. exists c. assumption.
  - intros c [H3 H4]. apply H2; assumption.
Qed.

Proposition IsEquiv : forall (a:U), Choice -> a :~: card a.
Proof.
  intros a AC.
  remember (fun b => Ordinal b /\ a :~: b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. {
    rewrite H1. apply CEM.HasElem, HasOrdinal. assumption. }
  assert (A (card a)) as H4. {
    unfold card. rewrite <- H1. apply SOI.IsIn; assumption. }
  rewrite H1 in H4. apply H4.

Qed.

Proposition IsEquivOrd : forall (a:U), Ordinal a -> a :~: card a.
  intros a G1.
  remember (fun b => Ordinal b /\ a :~: b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. {
    rewrite H1. apply CEM.HasElem. exists a. split. 1: assumption.
    apply Equiv.Refl. }
  assert (A (card a)) as H4. {
    unfold card. rewrite <- H1. apply SOI.IsIn; assumption. }
  rewrite H1 in H4. apply H4.
Qed.

Proposition IsNotEquiv : forall (a b:U), Ordinal b ->
  b :< card a -> a :<>: b.
Proof.
  intros a b H1 H2 H3.
  assert (card a :<=: b) as H4. { apply IsLowerBound; assumption. }
  assert (b :< b) as H5. { apply H4. assumption. }
  revert H5. apply NoElemLoop1.
Qed.

Proposition IsIncl : forall (a:U), Ordinal a -> card a :<=: a.
Proof.
  intros a H1. apply IsLowerBound. 1: assumption. apply Equiv.Refl.
Qed.

Proposition CardIsOrd : Cardinal :<=: Ordinal.
Proof.
  intros b [a H1]. subst. apply IsOrdinal.
Qed.


Proposition WhenCardinal : forall (a:U), Cardinal a <-> a = card a.
Proof.
  intros a. split; intros H1.
  - destruct H1 as [b H1]. apply Incl.DoubleInclusion. split.
    + remember (card a) as c eqn:H2. rewrite H1, H2.
      apply IsLowerBound. 1: apply IsOrdinal.
      apply Equiv.Tran with a.
Admitted.


