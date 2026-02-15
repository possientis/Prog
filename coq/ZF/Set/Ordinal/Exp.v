Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Exp.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Exp.
Export ZF.Notation.Exp.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module COE := ZF.Class.Ordinal.Exp.
Module CRD := ZF.Class.Relation.Domain.
Module CRL := ZF.Class.Relation.Functional.
Module SEM := ZF.Set.Empty.
Module SOG := ZF.Set.Ordinal.UnionGenOfClass.
Module SRD := ZF.Set.Relation.Domain.
Module SRL := ZF.Set.Relation.Functional.
Module SUG := ZF.Set.UnionGenOfClass.

(* The exponentiation of two ordinals when a is an ordinal.                     *)
Definition exp (a b:U) : U := (COE.Exp a)!b.

(* Notation "a :^: b" := (exp a b)                                              *)
Global Instance SetExp : Exp U := { exp := exp }.

Proposition WhenZeroR : forall (a:U), a :^: :0: = :1:.
Proof.
  intros a. apply COE.WhenZero.
Qed.

Proposition WhenSuccR : forall (a b:U), Ordinal b ->
  a :^: (succ b) = a :^: b :*: a.
Proof.
  apply COE.WhenSucc.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  :0: :< a  -> a :^: b = :\/:_{b} (COE.Exp a).
Proof.
  intros a b H1 H2.
  apply COE.WhenLimit. 1: assumption. apply SEM.HasElem.
  exists :0:. assumption.
Qed.

Proposition WhenLimitZero : forall (a b:U), Limit b ->
  a = :0: -> a :^: b  = :0:.
Proof.
  apply COE.WhenLimitZero.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :< a -> :0: :^: a = :0:.
Proof.
  intros a H1 H2.
  assert (Successor a \/ Limit a) as H3. { apply Limit.TwoWay; assumption. }
  destruct H3 as [H3|H3].
  - destruct H3 as [H [b H4]].
    rewrite H4, WhenSuccR, Mult.WhenZeroR. 1: reflexivity.
    subst. apply Succ.IsOrdinalRev. assumption.
  - rewrite WhenLimitZero; try reflexivity. assumption.
Qed.

Proposition IsOrdinal : forall (a b :U), Ordinal a -> Ordinal b ->
  Ordinal (a :^: b).
Proof.
  intros a b H1. revert b.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  apply Induction2.Induction.
  - rewrite WhenZeroR. apply Natural.OneIsOrdinal.
  - intros b H2 IH. rewrite WhenSuccR. 2: assumption.
    apply Mult.IsOrdinal; assumption.
  - intros b H2 IH.
    assert (a = :0: \/ :0: :< a) as H3. { apply Core.ZeroOrElem. assumption. }
    destruct H3 as [H3|H3].
    + subst. rewrite WhenLimitZero; try assumption. reflexivity.
    + rewrite WhenLimit; try assumption. apply SOG.IsOrdinal. apply IH.
Qed.

Proposition WhenOneL : forall (a:U), Ordinal a ->
  :1: :^: a = :1:.
Proof.
  assert (Ordinal :1:) as G1. { apply Natural.OneIsOrdinal. }
  assert (:0: :< :1:) as G2. { apply Succ.IsIn. }
  apply Induction2.Induction.
  - apply WhenZeroR.
  - intros a H1 IH.
    assert (Ordinal (:1: :^: a)) as G3. { apply IsOrdinal; assumption. }
    rewrite WhenSuccR, Mult.WhenOneR; assumption.
  - intros a H1 IH.
    rewrite WhenLimit; try assumption.
    apply DoubleInclusion. split; intros x H2.
    + apply SUG.Charac in H2. destruct H2 as [y [H2 H3]].
      assert (x :< :1: :^: y) as H4. { apply H3. }
      rewrite IH in H4; assumption.
    + apply SUG.Charac. exists :0:. split.
      * apply Limit.HasZero. assumption.
      * assert (x :< :1: :^: :0:) as X. 2: apply X. rewrite IH. 1: assumption.
        apply Limit.HasZero. assumption.
Qed.

Proposition WhenOneR : forall (a:U), Ordinal a ->
  a :^: :1: = a.
Proof.
  intros a H1.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (a :^: (succ :0:) = a) as X. 2: apply X.
  rewrite WhenSuccR, WhenZeroR, Mult.WhenOneL; try assumption. reflexivity.
Qed.

Proposition OneIsIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  :1: :<=: a -> :1: :<=: a :^: b.
Proof.
  intros a b H1. revert b.
  assert (Ordinal :1:) as G1. { apply Natural.OneIsOrdinal. }
  assert (Ordinal :0:) as G2. { apply Core.ZeroIsOrdinal. }
  remember (fun b => :1: :<=: a -> :1: :<=: a :^: b) as A eqn:H2.
  assert (forall b, Ordinal b -> A b) as X. 2: { rewrite H2 in X. assumption. }
  apply Induction2.Induction; rewrite H2.
  - intros _. rewrite WhenZeroR. apply Incl.Refl.
  - intros b H3 IH H4. rewrite WhenSuccR. 2: assumption.
    assert (Ordinal (a :^: b)) as G3. { apply IsOrdinal; assumption. }
    apply Incl.Tran with (:1: :*: a).
    + apply Mult.IsInclR; try assumption. apply Succ.ElemIsIncl; assumption.
    + apply Mult.InclCompatL; try assumption. apply IH. assumption.
  - intros b H3 IH H4 x H5.
    rewrite WhenLimit. 2: assumption. 2: { apply Succ.ElemIsIncl; assumption. }
    apply SUG.Charac. exists :0:. split.
    + apply Limit.HasZero. assumption.
    + assert (x :< a :^: :0:) as X. 2: apply X.
      rewrite WhenZeroR. assumption.
Qed.

Proposition HasZero : forall (a b:U), Ordinal a -> Ordinal b ->
  :0: :< a -> :0: :< a :^: b.
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal (a :^: b)) as G2. { apply IsOrdinal; assumption. }
  apply Succ.ElemIsIncl; try assumption.
  apply OneIsIncl; try assumption.
  apply Succ.ElemIsIncl; assumption.
Qed.

Proposition ElemCompatR : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  :1: :< c              ->
  a :< b                ->
  c :^: a :< c :^: b.
Proof.
  intros a b c H1 H2 H3 H4 H5. revert b H2 H5.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (Ordinal (succ a)) as G3. { apply Succ.IsOrdinal. assumption. }
  assert (:0: :< c) as G4. {
    apply Succ.ElemIsIncl; try assumption.
    apply Core.ElemIsIncl; assumption. }
  remember (fun b => c :^: a :< c :^: b) as A eqn:H6.
  assert (forall (d:U), Ordinal d -> c :^: d :< c :^: (succ d)) as H7. {
    intros d H7.
    assert (Ordinal (c :^: d)) as H8. { apply IsOrdinal; assumption. }
    assert (c :^: d :*: :1: :< c :^: d :*: c) as H9. {
      apply Mult.ElemCompatR; try assumption.
      apply Succ.ElemIsIncl; try assumption.
      apply OneIsIncl; try assumption.
      apply Core.ElemIsIncl; assumption. }
    rewrite Mult.WhenOneR in H9. 2: assumption.
    rewrite WhenSuccR; assumption. }
  assert (forall b, Ordinal b -> succ a :<=: b -> A b) as H8. {
    apply Induction2'. 1: assumption.
    - rewrite H6. apply H7. assumption.
    - rewrite H6. intros b H8 H9 IH.
      assert (Ordinal (succ b)) as G5. { apply Succ.IsOrdinal. assumption. }
      assert (Ordinal (c :^: a)) as G6. { apply IsOrdinal; assumption. }
      assert (Ordinal (c :^: b)) as G7. { apply IsOrdinal; assumption. }
      assert (Ordinal (c :^: succ b)) as G8. { apply IsOrdinal; assumption. }
      apply Core.ElemElemTran with (c :^: b); try assumption.
      apply H7. assumption.
    - rewrite H6. intros b H8 H9 IH.
      rewrite (WhenLimit c b); try assumption.
      apply SUG.Charac. exists (succ a). split.
      + apply Limit.HasSucc. 1: assumption.
        apply Succ.ElemIsIncl; try assumption. apply H8.
      + apply H7. assumption. }
  rewrite H6 in H8. intros b H9 H10. apply H8. 1: assumption.
  apply Succ.ElemIsIncl; assumption.
Qed.

Proposition InclCompatR : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  :0: :< c              ->
  a :<=: b              ->
  c :^: a :<=: c :^: b.
Proof.
  intros a b c H1 H2 H3 H4 H5.
  assert (Ordinal (c :^: b)) as G1. { apply IsOrdinal; assumption. }
  assert (c = :1: \/ :1: :< c) as H6. {
    apply Natural.OneOrElem; assumption. }
  destruct H6 as [H6|H6].
  - subst. rewrite WhenOneL, WhenOneL; try assumption. apply Incl.Refl.
  - apply Core.EqualOrElem in H5; try assumption.
    destruct H5 as [H5|H5].
    + subst. apply Incl.Refl.
    + apply Core.ElemIsIncl; try assumption.
      apply ElemCompatR; assumption.
Qed.

Proposition ElemCompatRevR : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  :1: :< c              ->
  c :^: a :< c :^: b    ->
  a :< b.
Proof.
  intros a b c H1 H2 H3 H4 H5.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (a :< b \/ b :<=: a) as H6. { apply Core.ElemOrIncl; assumption. }
  destruct H6 as [H6|H6]. 1: assumption. exfalso.
  assert (c :^: b :<=: c :^: a) as H7. {
    apply InclCompatR; try assumption.
    apply Core.ElemElemTran with :1:; try assumption.
    apply Succ.IsIn. }
  assert (c :^: a :< c :^: a) as H8. { apply H7. assumption. }
  revert H8. apply NoElemLoop1.
Qed.

Proposition InclCompatL : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  a :<=: b              ->
  a :^: c :<=: b :^: c.
Proof.
  intros a b c H1 H2 H3 H4. revert c H3.
  apply Induction2.Induction.
  - rewrite WhenZeroR, WhenZeroR. apply Incl.Refl.
  - intros c H3 IH.
    assert (Ordinal (a :^: c)) as G1. { apply IsOrdinal; assumption. }
    assert (Ordinal (b :^: c)) as G2. { apply IsOrdinal; assumption. }
    rewrite WhenSuccR, WhenSuccR; try assumption.
    apply Mult.InclCompat; assumption.
  - intros c H3 IH.
    assert (Ordinal c) as G1. { apply H3. }
    assert (Ordinal (a :^: c)) as G2. { apply IsOrdinal; assumption. }
    assert (Ordinal (b :^: c)) as G3. { apply IsOrdinal; assumption. }
    assert (a = :0: \/ :0: :< a) as H5. { apply Core.ZeroOrElem. assumption. }
    destruct H5 as [H5|H5].
    + subst. rewrite WhenZeroL. 2: assumption.
      * apply Core.IsIncl. assumption.
      * apply Limit.HasZero. assumption.
    + intros y H6.
      rewrite WhenLimit in H6; try assumption.
      apply SUG.Charac in H6. destruct H6 as [x [H6 H7]].
      assert (:0: :< b) as H8. { apply H4. assumption. }
      rewrite WhenLimit; try assumption.
      apply SUG.Charac. exists x. split. 1: assumption.
      apply IH; assumption.
Qed.

Proposition ElemCompatRevL : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  a :^: c :<  b :^: c   ->
  a :< b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (a :< b \/ b :<=: a) as H5. { apply Core.ElemOrIncl; assumption. }
  destruct H5 as [H5|H5]. 1: assumption. exfalso.
  assert (b :^: c :<=: a :^: c) as H6. { apply InclCompatL; assumption. }
  assert (a :^: c :< a :^: c) as H7. { apply H6. assumption. }
  revert H7. apply NoElemLoop1.
Qed.

Proposition ElemCompatL : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Successor c           ->
  a :< b                ->
  a :^: c :< b :^: c.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (Ordinal c) as H5. { apply H3. }
  destruct H3 as [H3 [d H6]]. subst.
  assert (Ordinal d) as H7. { apply Succ.IsOrdinalRev. assumption. }
  assert (Ordinal (a :^: succ d)) as G1. { apply IsOrdinal; assumption. }
  assert (Ordinal (b :^: succ d)) as G2. { apply IsOrdinal; assumption. }
  assert (Ordinal (b :^: d)) as G3. { apply IsOrdinal; assumption. }
  assert (Ordinal (a :^: d)) as G4. { apply IsOrdinal; assumption. }
  assert (Ordinal (b :^: d :*: a)) as G5. { apply Mult.IsOrdinal; assumption. }
  assert (a :^: d :<=: b :^: d) as H8. {
    apply InclCompatL; try assumption. apply Core.ElemIsIncl; assumption. }
  apply InclElemTran with (b :^: d :*: a); try assumption.
  - rewrite WhenSuccR. 2: assumption. apply Mult.InclCompatL; assumption.
  - rewrite WhenSuccR. 2: assumption. apply Mult.ElemCompatR; try assumption.
    apply HasZero; try assumption. apply Core.HasZero. 1: assumption.
    apply SEM.HasElem. exists a. assumption.
Qed.

Proposition IsIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  :1: :< a -> b :<=: a :^: b.
Proof.
  intros a b H1 H2 H3. revert b H2.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (:0: :< a) as G3. {
    apply Core.ElemElemTran with :1:; try assumption. apply Succ.IsIn. }
  apply Induction2.Induction.
  - rewrite WhenZeroR. apply Empty.IsIncl.
  - intros b H2 IH.
    assert (Ordinal (a :^: b)) as G4. { apply IsOrdinal; assumption. }
    assert (Ordinal (succ b)) as G5. { apply Succ.IsOrdinal. assumption. }
    assert (Ordinal (a :^: succ b)) as G6. { apply IsOrdinal; assumption. }
    apply Incl.Tran with (succ (a :^: b)).
    + apply Succ.InclCompat; assumption.
    + apply Succ.ElemIsIncl; try assumption.
      apply ElemCompatR; try assumption. apply Succ.IsIn.
  - intros b H2 IH c H4.
    rewrite WhenLimit; try assumption.
    apply SUG.Charac. exists (succ c). split.
    + apply Limit.HasSucc; assumption.
    + apply IH.
      * apply Limit.HasSucc; assumption.
      * apply Succ.IsIn.
Qed.

Proposition InBetween : forall (a b:U),
  Ordinal a             ->
  Ordinal b             ->
  :1: :< a              ->
  :0: :< b              ->
  exists d,
    Ordinal d           /\
    a :^: d :<=: b      /\
    b :< a :^: succ d.
Proof.
  intros a b H1 H2 H3 H4.
  remember (fun c => Ordinal c /\ b :< a :^: c) as A eqn:H5.
  assert (Ordinal (succ b)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (a :^: b)) as G2. { apply IsOrdinal; assumption. }
  assert (Ordinal (a :^: succ b)) as G3. { apply IsOrdinal; assumption. }
  assert (Ordinal :0:) as G4. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G5. { apply Natural.OneIsOrdinal. }
  assert (:0: :< a) as G6. {
    apply Core.ElemElemTran with :1:; try assumption. apply Succ.IsIn. }
  assert (A :<=: Ordinal) as H6. { intros c H6. rewrite H5 in H6. apply H6. }
  assert (A :<>: :0:) as H7. {
    apply CEM.HasElem. exists (succ b). rewrite H5. split. 1: assumption.
    apply Core.InclElemTran with (a :^: b); try assumption.
    - apply IsIncl; assumption.
    - apply ElemCompatR; try assumption. apply Succ.IsIn. }
  assert (exists c, Ordinal c /\ A c /\ forall d, A d -> c :<=: d) as H8. {
    apply Core.HasMinimal; assumption. }
    destruct H8 as [c [_ [H8 H9]]]. rewrite H5 in H8. destruct H8 as [H8 H10].
  assert (~ Limit c) as H11. {
    intros H11.
    rewrite WhenLimit in H10; try assumption.
    apply SUG.Charac in H10. destruct H10 as [d [H10 H12]].
    assert (Ordinal d) as H13. { apply Core.IsOrdinal with c; assumption. }
    assert (A d) as H14. { rewrite H5. split; assumption. }
    assert (c :<=: d) as H15. { apply H9. assumption. }
    assert (d :< d) as H16. { apply H15. assumption. }
    revert H16. apply NoElemLoop1. }
  assert (c <> :0:) as H12. {
    intros H12. rewrite H12 in H10. rewrite WhenZeroR in H10.
    rewrite Natural.OneExtension in H10.
    apply Single.Charac in H10. rewrite H10 in H4.
    apply SEM.Charac in H4. contradiction. }
  assert (Successor c) as H13. {
    assert (c = :0: \/ Successor c \/ Limit c) as H13. {
      apply Limit.ThreeWay. assumption. }
    destruct H13 as [H13|[H13|H13]]; try contradiction. assumption. }
  destruct H13 as [H13 [d H14]].
  assert (Ordinal d) as H15. { apply Succ.IsOrdinalRev. subst. assumption. }
  assert (Ordinal (a :^: d)) as G7. { apply IsOrdinal; assumption. }
  assert (b :< a :^: succ d) as H16. { rewrite H14 in H10. assumption. }
  assert (a :^: d :<=: b) as H17. {
    assert (b :< a :^: d \/ a :^: d :<=: b) as H17. {
      apply Core.ElemOrIncl; assumption. }
    destruct H17 as [H17|H17]. 2: assumption. exfalso.
    assert (A d) as H18. { rewrite H5. split; assumption. }
    assert (c :<=: d) as H19. { apply H9. assumption. }
    assert (d :< d) as H20. { apply H19. rewrite H14. apply Succ.IsIn. }
    revert H20. apply NoElemLoop1. }
  exists d. split. 1: assumption. split; assumption.
Qed.

Proposition IsLimitR : forall (a b:U), Ordinal a ->
  :1: :< a -> Limit b -> Limit (a :^: b).
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal b) as G1. { apply H3. }
  assert (Ordinal (a :^: b)) as G2. { apply IsOrdinal; assumption. }
  assert (a :^: b = :0: \/ Successor (a :^: b) \/ Limit (a :^: b)) as H4. {
    apply Limit.ThreeWay. assumption. }
  destruct H4 as [H4|[H4|H4]]. 3: assumption.
  - exfalso.
    assert (:1: :<=: a :^: b) as H5. {
      apply OneIsIncl; try assumption. apply Core.ElemIsIncl; assumption. }
    assert (:0: :< :0:) as H6. { rewrite H4 in H5. apply H5. apply Succ.IsIn. }
    revert H6. apply NoElemLoop1.
  - exfalso. destruct H4 as [H4 [d H5]].
    assert (Ordinal d) as G3. {
      apply Succ.IsOrdinalRev. rewrite <- H5. assumption. }
    assert (Ordinal :0:) as G4. { apply Core.ZeroIsOrdinal. }
    assert (Ordinal :1:) as G5. { apply Natural.OneIsOrdinal. }
    assert (:0: :< a) as G6. {
      apply Core.ElemElemTran with :1:; try assumption. apply Succ.IsIn. }
    assert (d :< a :^: b) as H6. { rewrite H5. apply Succ.IsIn. }
    rewrite WhenLimit in H6; try assumption.
    apply SUG.Charac in H6. destruct H6 as [c [H6 H7]].
    assert (Ordinal c) as G7. { apply Core.IsOrdinal with b; assumption. }
    assert (Ordinal (succ d)) as G8. { rewrite <- H5. assumption. }
    assert (Ordinal (a :^: c)) as G9. { apply IsOrdinal; assumption. }
    assert (a :^: c :< a :^: b) as H8. { apply ElemCompatR; assumption. }
    assert (succ d :< succ d) as H9. {
      apply Core.InclElemTran with (a :^: c); try assumption.
      - apply Succ.ElemIsIncl; assumption.
      - rewrite <- H5. assumption. }
    revert H9. apply NoElemLoop1.
Qed.

Proposition IsLimitL : forall (a b:U), Ordinal b ->
  :0: :< b -> Limit a -> Limit (a :^: b).
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal a) as G1. { apply H3. }
  assert (Successor b \/ Limit b) as H4. { apply Limit.TwoWay; assumption. }
  destruct H4 as [H4|H4].
  - destruct H4 as [H4 [d H5]]. subst.
    assert (Ordinal d) as G2. { apply Succ.IsOrdinalRev. assumption. }
    assert (Ordinal (a :^: d)) as G3. { apply IsOrdinal; assumption. }
    assert (Ordinal :0:) as G4. { apply Core.ZeroIsOrdinal. }
    assert (Ordinal :1:) as G5. { apply Natural.OneIsOrdinal. }
    rewrite WhenSuccR. 2: assumption.
    apply Mult.IsLimit; try assumption.
    apply Core.ElemInclTran with :1:; try assumption. 1: apply Succ.IsIn.
    apply OneIsIncl; try assumption.
    apply Core.ElemIsIncl. 1: assumption.
    apply Limit.HasOne. assumption.
  - apply IsLimitR; try assumption. apply Limit.HasOne. assumption.
Qed.

(* Not quite a distributivity property of course.                               *)
Proposition DistribL : forall (a b c:U),
  Ordinal a                               ->
  Ordinal b                               ->
  Ordinal c                               ->
  a :^: (b :+: c) = a :^: b :*: a :^: c.
Proof.
  intros a b c H1 H2. revert c.
  assert (Ordinal (a :^: b)) as G1. { apply IsOrdinal; assumption. }
  apply Induction2.Induction.
  - rewrite Plus.WhenZeroR, WhenZeroR, Mult.WhenOneR. 2: assumption. reflexivity.
  - intros c H3 IH.
    assert (Ordinal (a :^: c)) as G2. { apply IsOrdinal; assumption. }
    assert (Ordinal (b :+: c)) as G3. { apply Plus.IsOrdinal; assumption. }
    rewrite WhenSuccR, <- Mult.Assoc, <- IH, Plus.WhenSuccR; try assumption.
    apply WhenSuccR. assumption.
  - intros c H3 IH.
    assert (Limit (b :+: c)) as H4. { apply Plus.IsLimit; assumption. }
    assert (Ordinal c) as G4. { apply H3. }
    assert (Ordinal (b :+: c)) as G5. { apply H4. }
    assert (:0: :< c) as G6. { apply Limit.HasZero. assumption. }
    assert (:0: :< b :+: c) as G7. { apply Limit.HasZero. assumption. }
    assert (a = :0: \/ :0: :< a) as H5. { apply Core.ZeroOrElem. assumption. }
    destruct H5 as [H5|H5].
    + subst. rewrite WhenZeroL, (WhenZeroL c), Mult.WhenZeroR; try assumption.
      reflexivity.
    + assert (a = :1: \/ :1: :< a) as H6. {
        apply Natural.OneOrElem; assumption. }
      destruct H6 as [H6|H6].
      * subst. rewrite WhenOneL, WhenOneL, WhenOneL, Mult.WhenOneR;
        try assumption. reflexivity.
      * assert (Limit (a :^: c)) as H7. { apply IsLimitR; assumption. }
        assert (Ordinal (a :^: c)) as G9. { apply IsOrdinal; assumption. }
        rewrite WhenLimit; try assumption.
        rewrite Mult.WhenLimit. 2: assumption.
        apply DoubleInclusion. split; intros y H8;
        apply SUG.Charac; apply SUG.Charac in H8.
        { destruct H8 as [e [H8 H9]].
          assert (Ordinal e) as G8. {
            apply Core.IsOrdinal with (b :+: c); assumption. }
          assert (y :< a :^: e) as H10. { assumption. } clear H9.
          assert (e :<=: b \/ b :<=: e) as H11. { apply Core.InclOrIncl; assumption. }
          destruct H11 as [H11|H11].
          - exists :1:. split.
            + apply Limit.HasOne. assumption.
            + assert (y :< a :^: b :*: :1:) as X. 2: apply X.
              assert (a :^: e :<=: a :^: b) as H12. { apply InclCompatR; assumption. }
              rewrite Mult.WhenOneR. 2: assumption. apply H12. assumption.
          - assert (exists f, Ordinal f /\ b :+: f = e) as H12. {
              apply Plus.CompleteR; assumption. }
            destruct H12 as [f [H12 H13]].
            assert (f :< c) as H14. {
              apply Plus.ElemCompatRevR with b; try assumption.
              rewrite H13. assumption. }
            assert (a :^: (b :+: f) = a :^: b :*: a :^: f) as H15. {
              apply IH. assumption. }
            exists (a :^: f). split.
            + apply ElemCompatR; assumption.
            + assert (y :< a :^: b :*: a :^: f) as X. 2: apply X.
              rewrite <- H15, H13. assumption. }
        { destruct H8 as [d [H8 H9]].
          assert (Ordinal d) as G8. {
            apply Core.IsOrdinal with (a :^: c); assumption. }
          rewrite WhenLimit in H8; try assumption.
          apply SUG.Charac in H8.
          destruct H8 as [f [H8 H10]].
          assert (Ordinal f) as G10. { apply Core.IsOrdinal with c; assumption. }
          assert (Ordinal (a :^: f)) as G11. { apply IsOrdinal; assumption. }
          exists (b :+: f). split.
          - apply Plus.ElemCompatR; assumption.
          - assert (y :< a :^: (b :+: f)) as X. 2: apply X.
            rewrite IH. 2: assumption.
            assert (d :< a :^: f) as H11. { assumption. } clear H10.
            assert (y :< a :^: b :*: d) as H12. { assumption. } clear H9.
            assert (a :^: b :*: d :<=: a :^: b :*: a :^: f) as H13. {
              apply Mult.InclCompatR; try assumption.
              apply Core.ElemIsIncl; assumption. }
            apply H13. assumption. }
Qed.

(* Not quite an associativity property of course.                               *)
Proposition Assoc : forall (a b c:U),
  Ordinal a                               ->
  Ordinal b                               ->
  Ordinal c                               ->
  (a :^: b) :^: c = a :^: (b :*: c).
Proof.
  intros a b c H1 H2. revert c.
  apply Induction2.Induction.
  - rewrite WhenZeroR, Mult.WhenZeroR, WhenZeroR. reflexivity.
  - intros c H3 IH.
    assert (Ordinal (b :*: c)) as G1. { apply Mult.IsOrdinal; assumption. }
    rewrite WhenSuccR, IH, <- DistribL, <- Mult.WhenSuccR; try assumption.
    reflexivity.
  - intros c H3 IH.
    assert (Ordinal c) as G1. { apply H3. }
    assert (Ordinal (b :*: c)) as G2. { apply Mult.IsOrdinal; assumption. }
    assert (:0: :< c) as G3. { apply Limit.HasZero. assumption. }
    assert (b = :0: \/ :0: :< b) as H4. { apply Core.ZeroOrElem. assumption. }
    destruct H4 as [H4|H4].
    + subst. rewrite WhenZeroR, WhenOneL, Mult.WhenZeroL, WhenZeroR;
      try assumption. reflexivity.
    + assert (Limit (b :*: c)) as H5. { apply Mult.IsLimit; assumption. }
      assert (:0: :< b :*: c) as G4. { apply Limit.HasZero. assumption. }
      assert (a = :0: \/ :0: :< a) as H6. { apply Core.ZeroOrElem. assumption. }
      destruct H6 as [H6|H6].
      * subst. rewrite WhenZeroL, WhenZeroL, WhenZeroL; try assumption.
        reflexivity.
      * assert (Ordinal (a :^: b)) as G5. { apply IsOrdinal; assumption. }
        assert (:0: :< a :^: b) as G6. { apply HasZero; assumption. }
        apply DoubleInclusion. split; intros y H7;
        rewrite WhenLimit in H7; try assumption;
        rewrite WhenLimit; try assumption;
        apply SUG.Charac in H7;
        apply SUG.Charac.
        { destruct H7 as [d [H7 H8]]. exists (b :*: d). split.
          assert (Ordinal d) as G7. { apply Core.IsOrdinal with c; assumption. }
          - apply Mult.ElemCompatR; assumption.
          - assert (y :< (a :^: b) :^: d) as H9. { assumption. } clear H8.
            assert (y :< a :^: (b :*: d)) as X. 2: apply X.
            rewrite <- IH; assumption. }
        { destruct H7 as [e [H7 H8]].
          assert (Ordinal e) as G7. {
            apply Core.IsOrdinal with (b :*: c); assumption. }
          assert (y :< a :^: e) as H9. { assumption. } clear H8.
          rewrite Mult.WhenLimit in H7. 2: assumption.
          apply SUG.Charac in H7. destruct H7 as [d [H7 H8]].
          assert (Ordinal d) as G8. { apply Core.IsOrdinal with c; assumption. }
          assert (Ordinal (b :*: d)) as G9. { apply Mult.IsOrdinal; assumption. }
          assert (e :< b :*: d) as H10. { assumption. } clear H8.
          exists d. split. 1: assumption.
          assert (y :< (a :^: b) :^: d) as X. 2: apply X.
          rewrite IH. 2: assumption.
          assert (a :^: e :<=: a :^: (b :*: d)) as H11. {
            apply InclCompatR; try assumption.
            apply Core.ElemIsIncl; assumption. }
          apply H11. assumption. }
Qed.
