Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Exp.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.ShiftL.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Decreasing.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Ordinal.OrdFunOn.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.ShiftL.
Require Import ZF.Set.Ordinal.ShiftR.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.SumOfClass.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
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
Module COL := ZF.Class.Ordinal.ShiftL.
Module COR := ZF.Class.Ordinal.ShiftR.
Module CRD := ZF.Class.Relation.Domain.
Module CRL := ZF.Class.Relation.Functional.
Module SEM := ZF.Set.Empty.
Module SOG := ZF.Set.Ordinal.UnionGenOfClass.
Module SOL := ZF.Set.Ordinal.ShiftL.
Module SOR := ZF.Set.Ordinal.ShiftR.
Module SRD := ZF.Set.Relation.Domain.
Module SRL := ZF.Set.Relation.Functional.

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

Proposition IsLess : forall (a b c d n:U),
  Ordinal a                                             ->
  Ordinal b                                             ->
  n :< :N                                               ->
  OrdFunOn c n                                          ->
  OrdFunOn d n                                          ->
  Decreasing d                                          ->
  :1: :< a                                              ->
  (forall i, i :< n -> c!i :< a)                        ->
  (forall i, i :< n -> d!i :< b)                        ->
  :sum:_{n} (:[fun i => a :^: d!i :*: c!i]:) :< a :^: b.
Proof.
  intros a b c d n H1 H2 H3 H4 H5 H6 H7.
  revert n H3 b c d H2 H4 H5 H6.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (:0: :< a) as G3. {
    apply Core.ElemElemTran with :1:; try assumption.
    apply Succ.IsIn. }
  remember (fun n =>
    forall b c d: U,
    Ordinal b ->
    OrdFunOn c n ->
    OrdFunOn d n ->
    Decreasing d ->
    (forall i, i :< n -> c!i :< a) ->
    (forall i, i :< n -> d!i :< b) ->
    :sum:_{ n} (:[ fun i => a :^: d!i :*: c!i ]:) :< a :^: b)
    as A eqn:H8.
  assert (forall n, n :< :N -> A n) as H9. {
    apply Omega.Induction; rewrite H8.
    - intros b c d H2 _ _ _ _ _.
      rewrite SumOfClass.WhenZero. apply HasZero; assumption.
    - intros n H3 IH b c d H2 H4 H5 H6 H9 H10.
      assert (Ordinal n) as G4. { apply Omega.HasOrdinalElem. assumption. }
      assert (Functional c) as G5. { apply H4. }
      assert (Functional d) as G6. { apply H5. }
      assert (domain c = succ n) as G7. { apply H4. }
      assert (domain d = succ n) as G8. { apply H5. }
      remember (fun i => a :^: d!i :*: c!i) as F eqn:E.
      assert (CRL.Functional :[F]:) as H11. { apply ToFun.IsFunctional. }
      assert (forall i, i :< succ n -> CRD.domain :[F]: i) as H12. {
          intros i _. apply ToFun.DomainOf. }
      assert (forall i, i :< succ n -> Ordinal c!i) as H13. {
        intros i H13. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
      assert (forall i, i :< succ n -> Ordinal d!i) as H14. {
        intros i H14. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
      assert (forall i : U, i :< succ n -> Ordinal (:[F]:!i)) as H15. {
          intros i H15. rewrite ToFun.Eval. rewrite E.
          apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption. apply H14. assumption.
          - apply H13. assumption. }
      rewrite SumOfClass.ShiftL, ToFun.Eval; try assumption.
      remember (shiftL c) as c' eqn:H16.
      remember (shiftL d) as d' eqn:H17.
      assert (OrdFunOn c' n) as H18. {
        rewrite H16. apply SOL.OnSucc. assumption. }
      assert (OrdFunOn d' n) as H19. {
        rewrite H17. apply SOL.OnSucc. assumption. }
      assert (Decreasing d') as H20. {
        rewrite H17. apply SOL.IsDecreasing. 2: assumption. apply H5. }
      assert (Ordinal d!:0:) as H21. {
        apply OrdFunOn.IsOrdinal with (succ n). 1: assumption.
        apply Succ.HasZero. assumption. }
      assert (forall i, i :< n -> c'!i :< a) as H22. {
        intros i H22.
        assert (Ordinal i) as G9. { apply Core.IsOrdinal with n; assumption. }
        rewrite H16, SOL.Eval. 2: assumption.
        - apply H9, Succ.ElemCompat; assumption.
        - rewrite G7. apply Succ.ElemCompat; assumption. }
      assert (forall i, i :< n -> d'!i :< d!:0:) as H23. {
        intros i H23.
        assert (Ordinal i) as G9. { apply Core.IsOrdinal with n; assumption. }
        rewrite H17, SOL.Eval. 2: assumption.
        - apply H6.
          + rewrite G8. apply Succ.HasZero. assumption.
          + rewrite G8. apply Succ.ElemCompat; assumption.
          + apply Succ.HasZero. assumption.
        - rewrite G8. apply Succ.ElemCompat; assumption. }
      remember (fun i => a :^: d'!i :*: c'!i) as G eqn:E'.
      assert (:sum:_{n} (COL.shiftL :[F]:) = :sum:_{n} :[G]:) as H24. {
        apply SumOfClass.EqualCharac. 1: assumption.
        intros i H24.
       assert (Ordinal i) as G9. { apply Core.IsOrdinal with n; assumption. }
        rewrite
          COL.Eval, ToFun.Eval, ToFun.Eval, E, E', H16, H17, SOL.Eval, SOL.Eval;
        try assumption. 1: reflexivity.
        - rewrite G7. apply Succ.ElemCompat; assumption.
        - rewrite G8. apply Succ.ElemCompat; assumption.
        - apply ToFun.DomainOf. }
      assert ((:sum:_{n} :[G]:) :< a :^: d!:0:) as H25. {
        rewrite E'. apply IH; assumption. }
      rewrite H24.
      assert (Ordinal (a :^: b)) as G9. { apply IsOrdinal; assumption. }
      assert (Ordinal (a :^: d!:0:)) as G10. { apply IsOrdinal; assumption. }
      assert (Ordinal (F :0:)) as G11. {
        rewrite E. apply Mult.IsOrdinal. 1: assumption.
        apply H13, Succ.HasZero. assumption. }
      assert (forall i, i :< n -> Ordinal c'!i) as G12. {
        intros i G12. apply Core.IsOrdinal with a. 1: assumption.
        apply H22. assumption. }
      assert (forall i, i :< n -> Ordinal d'!i) as G13. {
        intros i G13. apply Core.IsOrdinal with d!:0:. 1: assumption.
        apply H23. assumption. }
      assert (forall i, i :< n -> Ordinal (a :^: d'!i)) as G14. {
        intros i G14. apply IsOrdinal. 1: assumption.
        apply G13. assumption. }
      assert (forall i, i :< n -> Ordinal (G i)) as G15. {
        rewrite E'. intros i G15. apply Mult.IsOrdinal.
        - apply G14. assumption.
        - apply G12. assumption. }
      assert (Ordinal (:sum:_{n} :[G]:)) as G16. {
        apply SumOfClass.IsOrdinal. 1: assumption.
        intros i G16. rewrite ToFun.Eval. apply G15. assumption. }
      assert (Ordinal (F :0: :+: :sum:_{n} :[G]:)) as G17. {
        apply Plus.IsOrdinal; assumption. }
      assert (Ordinal (F :0: :+: a :^: d!:0:)) as G18. {
        apply Plus.IsOrdinal; assumption. }
      apply Core.ElemInclTran with (F :0: :+: a :^: d!:0:); try assumption.
      + apply Plus.ElemCompatR; assumption.
      + rewrite E.
        assert (
          a :^: d!:0: :*: (c!:0: :+: :1:)
        = a :^: d!:0: :*: c!:0: :+: a :^: d!:0:) as H26. {
          rewrite Mult.DistribL, Mult.WhenOneR; try assumption. 1: reflexivity.
          apply H13, Succ.HasZero. assumption. }
        rewrite <- H26, Plus.WhenOneR.
        assert (succ c!:0: :<=: a) as H27. {
          apply Succ.ElemIsIncl. 2: assumption.
          - apply H13, Succ.HasZero. assumption.
          - apply H9, Succ.HasZero. assumption. }
        assert (Ordinal (succ c!:0:)) as G19. {
          apply Succ.IsOrdinal. apply H13, Succ.HasZero. assumption. }
        apply Incl.Tran with (a :^: d!:0: :*: a).
        * apply Mult.InclCompatR; assumption.
        * rewrite <- WhenSuccR. 2: assumption.
          assert (Ordinal (succ d!:0:)) as G20. {
            apply Succ.IsOrdinal. assumption. }
          assert (succ d!:0: :<=: b) as H28. {
            apply Succ.ElemIsIncl; try assumption.
            apply H10, Succ.HasZero. assumption. }
          apply InclCompatR; assumption. }
  rewrite H8 in H9. assumption.
Qed.

Proposition Polynomial : forall (a b:U),
  Ordinal a                                             ->
  Ordinal b                                             ->
  :1: :< a                                              ->
  exists n c d,
    n :< :N                                             /\
    OrdFunOn c n                                        /\
    OrdFunOn d n                                        /\
    Decreasing d                                        /\
    (forall i, i :< n -> :0: :< c!i)                    /\
    (forall i, i :< n -> c!i :< a  )                    /\
    b = :sum:_{n} :[fun i => a :^: d!i :*: c!i]:.
Proof.
  intros a b H1 H2 H3. revert b H2.
  remember (fun b =>
    :0: :< b                                                    ->
    exists n c d,
      n :< :N                                                   /\
      OrdFunOn c n                                              /\
      OrdFunOn d n                                              /\
      Decreasing d                                              /\
      (forall i, i :< n -> :0: :< c!i)                          /\
      (forall i, i :< n -> c!i :< a)                            /\
      b = :sum:_{n} :[fun i => a :^: d!i :*: c!i]:) as A eqn:E.
  assert (forall b, Ordinal b -> A b) as H4. {
    apply Induction.Induction. intros b H2 IH. rewrite E. intros H4.
    assert (exists e,
      Ordinal e /\ a :^: e :<=: b /\ b :< a :^: succ e) as H5. {
        apply InBetween; assumption. }
      destruct H5 as [e [H5 [H6 H7]]].
    assert (Ordinal (a :^: e)) as G1. { apply IsOrdinal; assumption. }
    assert (Ordinal :0:) as G2. { apply Core.ZeroIsOrdinal. }
    assert (Ordinal :1:) as G3. { apply Natural.OneIsOrdinal. }
    assert (:0: :< a) as G4. {
      apply ElemElemTran with :1:; try assumption.
      apply Succ.IsIn. }
    assert (exists q r,
      Ordinal q                 /\
      Ordinal r                 /\
      b = a :^: e :*: q :+: r   /\
      r :< a :^: e) as H8. {
        apply Mult.Euclid; try assumption.
        apply HasZero; assumption. }
    destruct H8 as [q [r [H8 [H9 [H10 H11]]]]].
    assert (Ordinal (a :^: e :*: q)) as G5. {
      apply Mult.IsOrdinal; assumption. }
    assert (:0: :< q) as H12. {
      assert (q = :0: \/ :0: :< q) as H12. { apply Core.ZeroOrElem. assumption. }
      destruct H12 as [H12|H12]. 2: assumption. subst. exfalso.
      rewrite Mult.WhenZeroR, Plus.WhenZeroL in H6. 2: assumption.
      assert (r :< r) as H13. { apply H6. assumption. }
      revert H13. apply NoElemLoop1. }
    assert (q :< a) as H13. {
      assert (q :< a \/ a :<=: q) as H13. { apply Core.ElemOrIncl; assumption. }
      destruct H13 as [H13|H13]. 1: assumption. exfalso.
      assert (a :^: succ e :<=: b) as H14. {
        rewrite WhenSuccR, H10. 2: assumption.
        apply Incl.Tran with (a :^: e :*: q).
      - apply Mult.InclCompatR; assumption.
      - apply Plus.IsInclR; assumption. }
      assert (b :< b) as H15. { apply H14. assumption. }
      revert H15. apply NoElemLoop1. }
    assert (r = :0: \/ :0: :< r) as H14. { apply Core.ZeroOrElem. assumption. }
    assert (:1: :< :N) as G6. { apply Omega.HasOne. }
    assert (:1: = succ :0:) as G7. { reflexivity. }
    assert (Ordinal :0:) as G8. { apply Core.ZeroIsOrdinal. }
    destruct H14 as [H14|H14].
    - remember :{ :(:0:,q): }: as c eqn:H15.
      remember :{ :(:0:,e): }: as d eqn:H16.
      assert (OrdFunOn c :1:) as H17. {
        rewrite H15. apply OrdFunOn.WhenSingle with q.
        1: assumption. reflexivity. }
      assert (OrdFunOn d :1:) as H18. {
        rewrite H16. apply OrdFunOn.WhenSingle with e.
        1: assumption. reflexivity. }
      assert (Decreasing d) as H19. {
        rewrite H16. apply Decreasing.WhenSingle with :0: e. reflexivity. }
      assert (forall i, i :< :1: -> :0: :< c!i) as H20. {
        intros i H20. rewrite Natural.OneExtension in H20.
        apply Single.Charac in H20. rewrite H20. clear H20.
        rewrite (Eval.WhenSingle :0: q c); assumption. }
      assert (forall i, i :< :1: -> c!i :< a) as H21. {
        intros i H21. rewrite Natural.OneExtension in H21.
        apply Single.Charac in H21. rewrite H21. clear H21.
        rewrite (Eval.WhenSingle :0: q c); assumption. }
      exists :1:, c, d. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      split. 1: assumption.
      rewrite G7, SumOfClass.WhenSucc, SumOfClass.WhenZero, Plus.WhenZeroL;
      try assumption.
      rewrite ToFun.Eval, (Eval.WhenSingle :0: q c), (Eval.WhenSingle :0: e d);
      try assumption.
      + rewrite H14, Plus.WhenZeroR in H10. assumption.
      + rewrite ToFun.Eval, (Eval.WhenSingle :0: q c), (Eval.WhenSingle :0: e d);
        assumption.
    - assert (a :^: e :*: :1: :<=: a :^: e :*: q) as H15. {
        apply Mult.InclCompatR; try assumption.
        apply Succ.ElemIsIncl; assumption. }
      rewrite Mult.WhenOneR in H15. 2: assumption.
      assert (a :^: e :<=: b) as H16. {
        apply Incl.Tran with (a :^: e :*: q). 1: assumption.
        rewrite H10. apply Plus.IsInclR; assumption. }
      assert (r :< b) as H17. { apply H16. assumption. }
      assert (A r) as H18. { apply IH. assumption. }
      rewrite E in H18. specialize (H18 H14).
      destruct H18 as [n [c [d [H18 [H19 [H20 [H21 [H22 [H23 H24]]]]]]]]].
      assert (Ordinal n) as G23. { apply Omega.HasOrdinalElem. assumption. }
      remember (shiftR e d) as d' eqn:H25.
      remember (shiftR q c) as c' eqn:H26.
      exists (succ n), c', d'.
      assert (succ n :< :N) as G9. { apply Omega.HasSucc. assumption. }
      assert (OrdFunOn c' (succ n)) as H27. {
        rewrite H26. apply SOR.IsOrdFunOnNat; assumption. }
      assert (OrdFunOn d' (succ n)) as H28. {
        rewrite H25. apply SOR.IsOrdFunOnNat; assumption. }
      assert (forall i, i :< n -> d!i :< e) as H29. {
        intros i H29.
        assert (Ordinal d!i) as G10. {
          apply OrdFunOn.IsOrdinal with n; assumption. }
        assert (Ordinal (a :^: d!i)) as G11. { apply IsOrdinal; assumption. }
        apply ElemCompatRevR with a; try assumption.
        apply Core.InclElemTran with r; try assumption.
        apply Incl.Tran with (a :^: d!i :*: c!i).
        - apply Mult.IsInclR. 1: assumption.
          + apply OrdFunOn.IsOrdinal with n; assumption.
          + apply H22. assumption.
        - rewrite H24.
          assert (a :^: d!i :*: c!i
            = :[fun i => a :^: d!i :*: c!i]:!i) as H30. {
            symmetry. apply (ToFun.Eval (fun i => a :^: d!i :*: c!i)). }
          rewrite H30. apply SumOfClass.IsIncl; try assumption.
          + intros j H31. exists (a :^: d!j :*: c!j).
            apply ToFun.Charac2. reflexivity.
          + intros j H31. rewrite ToFun.Eval.
            apply Mult.IsOrdinal.
            * apply IsOrdinal. 1: assumption.
              apply OrdFunOn.IsOrdinal with n; assumption.
            * apply OrdFunOn.IsOrdinal with n; assumption. }
      assert (OrdFun c) as G10. { apply H19. }
      assert (OrdFun d) as G11. { apply H20. }
      assert (domain c = n) as G12. { apply H19. }
      assert (domain d = n) as G13. { apply H20. }
      assert (Functional c) as G14. { apply H19. }
      assert (Functional d) as G15. { apply H20. }
      assert (Ordinal :N) as G16. { apply Omega.IsOrdinal. }
      assert (domain c :<=: :N) as G17. {
        rewrite G12. apply Core.ElemIsIncl; assumption. }
      assert (domain d :<=: :N) as G18. {
        rewrite G13. apply Core.ElemIsIncl; assumption. }
      assert (Ordinal (succ n)) as G19. {
        apply Omega.HasOrdinalElem. assumption. }
      assert (Decreasing d') as H30. {
        rewrite H25. apply SOR.IsDecreasing; try assumption;
        rewrite G13;assumption. }
      assert (forall i, i :< succ n -> :0: :< c'!i) as H31. {
        intros i H31.
        assert (i :< :N) as G20. {
          apply Omega.IsIn with (succ n); assumption. }
        assert (Ordinal i) as G21. { apply Omega.HasOrdinalElem. assumption. }
        assert (i = :0: \/ :0: :< i) as H32. {
          apply Core.ZeroOrElem. assumption. }
        destruct H32 as [H32|H32].
        - rewrite H26, H32, SOR.EvalZero; assumption.
        - apply Omega.HasPred in H32. 2: assumption.
          destruct H32 as [j [H32 H33]].
          assert (Ordinal j) as G22. { apply Omega.HasOrdinalElem. assumption. }
          assert (j :< n) as G24. {
            apply Succ.ElemCompatRev; try assumption.
            rewrite <- H33. assumption. }
          rewrite H26, H33, SOR.EvalSucc; try assumption.
          + apply H22. assumption.
          + rewrite G12. assumption. }
      assert (forall i, i :< succ n -> c'!i :< a) as H32. {
        intros i H32.
        assert (i :< :N) as G20. {
          apply Omega.IsIn with (succ n); assumption. }
        assert (Ordinal i) as G21. { apply Omega.HasOrdinalElem. assumption. }
        assert (i = :0: \/ :0: :< i) as H33. {
          apply Core.ZeroOrElem. assumption. }
        destruct H33 as [H33|H33].
        - rewrite H26, H33, SOR.EvalZero; assumption.
        - apply Omega.HasPred in H33. 2: assumption.
          destruct H33 as [j [H33 H34]].
          assert (Ordinal j) as G22. { apply Omega.HasOrdinalElem. assumption. }
          assert (j :< n) as G24. {
            apply Succ.ElemCompatRev; try assumption.
            rewrite <- H34. assumption. }
          rewrite H26, H34, SOR.EvalSucc; try assumption.
          + apply H23. assumption.
          + rewrite G12. assumption. }
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. split. 1: assumption. split. 1: assumption.
      remember (fun i => a :^: d!i :*: c!i) as F eqn:H33.
      remember (fun i => a :^: d'!i :*: c'!i) as G eqn:H34.
      remember (COR.shiftR (a :^: e :*: q) :[F]:) as H eqn:H35.
      assert (:sum:_{succ n} (:[G]:) = :sum:_{succ n} H) as H36. {
        apply SumOfClass.EqualCharac. 1: assumption. intros i H36.
        rewrite H34, H35, ToFun.Eval, H25, H26.
        assert (i :< :N) as G20. {
          apply Omega.IsIn with (succ n); assumption. }
        assert (Ordinal i) as G21. { apply Omega.HasOrdinalElem. assumption. }
        assert (i = :0: \/ :0: :< i) as H37. {
          apply Core.ZeroOrElem. assumption. }
        destruct H37 as [H37|H37].
        - rewrite H37, SOR.EvalZero, SOR.EvalZero, COR.EvalZero; try assumption.
          1: reflexivity. apply ToFun.IsFunctional.
        - apply Omega.HasPred in H37. 2: assumption.
          destruct H37 as [j [H37 H38]].
          assert (Ordinal j) as G22. { apply Omega.HasOrdinalElem. assumption. }
          assert (j :< n) as G24. {
            apply Succ.ElemCompatRev; try assumption.
            rewrite <- H38. assumption. }
          assert (j :< domain c) as G25. { rewrite G12. assumption. }
          assert (j :< domain d) as G26. { rewrite G13. assumption. }
          rewrite H38, SOR.EvalSucc, SOR.EvalSucc, COR.EvalSucc, H33, ToFun.Eval;
          try assumption. 1: reflexivity.
          + apply ToFun.IsFunctional.
          + apply ToFun.DomainOf. }
      rewrite H36, H35.
      assert (:sum:_{succ n} (COS.shiftR (a :^: e :*: q) :[F]:)
        = a :^: e :*: q :+: :sum:_{n} :[F]:) as H37. {
          apply SumOfClass.ShiftR; try assumption.
          - apply ToFun.IsFunctional.
          - intros j H37. apply ToFun.DomainOf.
          - intros j H37. rewrite ToFun.Eval, H33.
            apply Mult.IsOrdinal.
            + apply IsOrdinal. 1: assumption.
              apply OrdFunOn.IsOrdinal with n; assumption.
            + apply OrdFunOn.IsOrdinal with n; assumption. }
      assert (b = :sum:_{succ n} (COS.shiftR (a :^: e :*: q) :[F]:)) as X. 2: apply X.
      rewrite H37, H10, H24. reflexivity. }
  intros b H2.
  assert (b = :0: \/ :0: :< b) as H5. { apply Core.ZeroOrElem. assumption. }
  destruct H5 as [H5|H5].
  - exists :0:, :0:, :0:.
    assert (:0: :< :N) as H6. { apply Omega.HasZero. }
    assert (OrdFunOn :0: :0:) as H7. { apply OrdFunOn.WhenEmpty. reflexivity. }
    assert (Decreasing :0:) as H8. { apply Decreasing.WhenEmpty. reflexivity. }
    assert (forall i, i :< :0: -> :0: :< :0:!i) as H9. {
      intros i H9. apply Empty.Charac in H9. contradiction. }
    assert (forall i, i :< :0: -> :0:!i :< a) as H10. {
      intros i H10. apply Empty.Charac in H10. contradiction. }
    split. 1: assumption. split. 1: assumption. split. 1: assumption.
    split. 1: assumption. split. 1: assumption. split. 1: assumption.
    rewrite H5, SumOfClass.WhenZero. reflexivity.
  - rewrite E in H4. apply H4; assumption.
Qed.

Proposition ExponentFirst : forall (a b c q1 q2 r1 r2:U),
  Ordinal a                                           ->
  Ordinal b                                           ->
  Ordinal c                                           ->
  Ordinal q1                                          ->
  Ordinal q2                                          ->
  Ordinal r1                                          ->
  Ordinal r2                                          ->
  :1: :< a                                            ->
  q1  :< a                                            ->
  r1  :< a :^: b                                      ->
  :0: :< q2                                           ->
  b   :< c                                            ->
  a :^: b :*: q1 :+: r1 :< a :^: c :*: q2 :+: r2.
Proof.
  intros a b c q1 q2 r1 r2 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
  assert (Ordinal (succ b)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (:0: :< a) as G2. { apply Natural.HasZero; assumption. }
  assert (Ordinal (a :^: c)) as G3. { apply IsOrdinal; assumption. }
  assert (Ordinal (a :^: c :*: q2)) as G4. { apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b)) as G5. { apply IsOrdinal; assumption. }
  assert (Ordinal (a :^: b :*: q1)) as G6. { apply Mult.IsOrdinal; assumption. }
  assert (succ q1 :<=: a) as G7. { apply Succ.ElemIsIncl; assumption. }
  assert (succ b :<=: c) as G8. { apply Succ.ElemIsIncl; assumption. }
  assert (Ordinal :1:) as G9. { apply Natural.OneIsOrdinal. }
  assert (Ordinal (a :^: b :*: q1 :+: r1)) as G10. {
    apply Plus.IsOrdinal; assumption. }
  assert (Ordinal (succ q1)) as G11. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (a :^: b :*: (succ q1))) as G12. {
    apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: b :*: a)) as G13. {
    apply Mult.IsOrdinal; assumption. }
  assert (Ordinal (a :^: (succ b))) as G14. { apply IsOrdinal; assumption. }
  assert (Ordinal (a :^: c :*: q2 :+: r2)) as G15. {
    apply Plus.IsOrdinal; assumption. }
  assert (a :^: succ b :<=: a :^: c) as H13. { apply InclCompatR; assumption. }
  assert (a :^: succ b :<=: a :^: c :*: q2) as H14. {
    apply Incl.Tran with (a :^: c). 1: assumption.
    apply Mult.IsInclR; assumption. }
  assert (a :^: succ b :<=: a :^: c :*: q2 :+: r2) as H15. {
    apply Incl.Tran with (a :^: c :*: q2). 1: assumption.
    apply Plus.IsInclR; assumption. }
  assert (a :^: b :*: q1 :+: r1 :< a :^: b :*: q1 :+: a :^: b) as H16. {
    apply Plus.ElemCompatR; assumption. }
  assert (a :^: b :*: q1 :+: r1 :< a :^: b :*: (succ q1)) as H17. {
    rewrite <- Plus.WhenOneR, Mult.DistribL, Mult.WhenOneR; assumption. }
  assert (a :^: b :*: q1 :+: r1 :< a :^: (succ b)) as H18. {
    rewrite <- Plus.WhenOneR, DistribL, WhenOneR; try assumption.
    apply Core.ElemInclTran with (a :^: b :*: (succ q1)); try assumption.
    apply Mult.InclCompatR; assumption. }
  apply Core.ElemInclTran with (a :^: (succ b)); assumption.
Qed.

Proposition PolynomialUnique : forall (a n m c d e f:U),
  Ordinal a                                       ->
  :1: :< a                                        ->
  n :< :N                                         ->
  m :< :N                                         ->
  OrdFunOn c n                                    ->
  OrdFunOn d n                                    ->
  OrdFunOn e m                                    ->
  OrdFunOn f m                                    ->
  Decreasing d                                    ->
  Decreasing f                                    ->
  (forall i, i :< n -> :0: :< c!i)                ->
  (forall i, i :< n -> c!i :< a  )                ->
  (forall i, i :< m -> :0: :< e!i)                ->
  (forall i, i :< m -> e!i :< a  )                ->
  :sum:_{n} (:[fun i => a :^: d!i :*: c!i]:) =
  :sum:_{m} (:[fun i => a :^: f!i :*: e!i]:)      ->
  n = m /\ c = e /\ d = f.
Proof.
  intros a n m c d e f H1 H2 H3. revert n H3 m c d e f.
  assert (Ordinal :0:) as K1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as K2. { apply Natural.OneIsOrdinal. }
  assert (:0: :< a) as K3. { apply Natural.HasZero; assumption. }
  remember (fun n =>
    forall m c d e f : U,
    m :< :N                                                             ->
    OrdFunOn c n                                                        ->
    OrdFunOn d n                                                        ->
    OrdFunOn e m                                                        ->
    OrdFunOn f m                                                        ->
    Decreasing d                                                        ->
    Decreasing f                                                        ->
    (forall i, i :< n -> :0: :< c!i)                                    ->
    (forall i, i :< n -> c!i :< a  )                                    ->
    (forall i, i :< m -> :0: :< e!i)                                    ->
    (forall i, i :< m -> e!i  :< a )                                    ->
    :sum:_{ n} (:[ fun i : U => a :^: (d) ! (i) :*: (c) ! (i) ]:) =
      :sum:_{ m} (:[ fun i : U => a :^: (f) ! (i) :*: (e) ! (i) ]:)     ->
    n = m /\ c = e /\ d = f) as A eqn:E.
  assert (forall n, n :< :N -> A n) as H3. {
    apply Omega.Induction; rewrite E.
    - intros m c d e f H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
      remember (fun i => a :^: d!i :*: c!i) as F1 eqn:E1.
      remember (fun i => a :^: f!i :*: e!i) as F2 eqn:E2.
      assert (Ordinal m) as G1. { apply Omega.HasOrdinalElem. assumption. }
      rewrite SumOfClass.WhenZero in H14.
      assert (:0: = m) as H15. {
        assert (m = :0: \/ :0: :< m) as H15. {
          apply Core.ZeroOrElem. assumption. }
        destruct H15 as [H15|H15]. 1: { symmetry. assumption. } exfalso.
        apply Omega.HasPred in H15. 2: assumption.
        destruct H15 as [k [H15 H16]].
        assert (Ordinal k) as G2. { apply Omega.HasOrdinalElem. assumption. }
        rewrite H16, SumOfClass.WhenSucc, ToFun.Eval in H14. 2: assumption.
        assert (k :< m) as G3. { rewrite H16. apply Succ.IsIn. }
        assert (Ordinal (e!k)) as G4. {
          apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (Ordinal (f!k)) as G5. {
          apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< m -> Ordinal (F2 i)) as G6. {
          intros i G6. rewrite E2. apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with m; assumption.
          - apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (Ordinal (F2 k)) as G7. { apply G6. assumption. }
        assert (Ordinal (:sum:_{k} :[F2]:)) as G8. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G8. rewrite ToFun.Eval. apply G6.
          apply Core.ElemElemTran with k; try assumption.
            apply Omega.HasOrdinalElem, Omega.IsIn with k; assumption. }
        assert (F2 k :<=: (:sum:_{k} :[F2]:) :+: F2 k) as H17. {
          apply Plus.IsInclL; assumption. }
        rewrite <- H14 in H17.
        assert (:0: :< F2 k) as H18. {
          rewrite E2. apply Mult.HasZero. 2: assumption.
          - apply IsOrdinal; assumption.
          - apply HasZero; assumption.
          - apply H12. assumption. }
        assert (:0: :< :0:) as H19. { apply H17. assumption. }
        apply Empty.Charac in H19. contradiction. }
        rewrite <- H15 in H6. rewrite <- H15 in H7.
        assert (c = :0:) as H20. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (d = :0:) as H21. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (e = :0:) as H22. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (f = :0:) as H23. { apply OrdFunOn.WhenEmpty. assumption. }
        assert (c = e) as H24. { subst. reflexivity. }
        assert (d = f) as H25. { subst. reflexivity. }
        split. 1: assumption. split; assumption.
    - intros n H3 IH m c d e f H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
      remember (fun i => a :^: d!i :*: c!i) as F1 eqn:E1.
      remember (fun i => a :^: f!i :*: e!i) as F2 eqn:E2.
      assert (Ordinal n) as G1. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal m) as G2. { apply Omega.HasOrdinalElem. assumption. }
      assert (succ n :< :N) as G3. { apply Omega.HasSucc. assumption. }
      assert (Ordinal (succ n)) as G4. {
        apply Omega.HasOrdinalElem. assumption. }
      assert (m =:0: \/ :0: :< m) as H16. { apply Core.ZeroOrElem. assumption. }
      destruct H16 as [H16|H16].
      + exfalso.
        rewrite H16, SumOfClass.WhenZero, SumOfClass.WhenSucc, ToFun.Eval in H15.
        2: assumption.
        assert (n :< succ n) as G5. { apply Succ.IsIn. }
        assert (Ordinal (c!n)) as G6. {
          apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (Ordinal (d!n)) as G7. {
          apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (forall i, i :< succ n -> Ordinal (F1 i)) as G8. {
          intros i G8. rewrite E1. apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with (succ n); assumption.
          - apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (Ordinal (F1 n)) as G9. { apply G8. assumption. }
        assert (Ordinal (:sum:_{n} :[F1]:)) as G10. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G10. rewrite ToFun.Eval. apply G8.
          apply Core.ElemElemTran with n; try assumption.
            apply Omega.HasOrdinalElem, Omega.IsIn with n; assumption. }
        assert (F1 n :<=: (:sum:_{n} :[F1]:) :+: F1 n) as H17. {
          apply Plus.IsInclL; assumption. }
        rewrite H15 in H17.
        assert (:0: :< F1 n) as H18. {
          rewrite E1. apply Mult.HasZero. 2: assumption.
          - apply IsOrdinal; assumption.
          - apply HasZero; assumption.
          - apply H11. assumption. }
        assert (:0: :< :0:) as H19. { apply H17. assumption. }
        apply Empty.Charac in H19. contradiction.
      + apply Omega.HasPred in H16. 2: assumption. destruct H16 as [k [H16 H17]].
        assert (forall i, i :< m -> Ordinal (F2 i)) as G5. {
          intros i G5. rewrite E2. apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with m; assumption.
          - apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< succ n -> Ordinal (F1 i)) as G6. {
          intros i G6. rewrite E1. apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption.
            apply OrdFunOn.IsOrdinal with (succ n); assumption.
          - apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (Functional c) as G7. { apply H5. }
        assert (Functional d) as G8. { apply H6. }
        assert (Functional e) as G9. { apply H7. }
        assert (Functional f) as G10. { apply H8. }
        assert (domain c = succ n) as G11. { apply H5. }
        assert (domain d = succ n) as G12. { apply H6. }
        assert (domain e = m) as G13. { apply H7. }
        assert (domain f = m) as G14. { apply H8. }
        assert (Ordinal k) as G15. { apply Omega.HasOrdinalElem. assumption. }
        assert (F1 :0: :+: (:sum:_{n} (COL.shiftL :[F1]:))
          = F2 :0: :+: (:sum:_{k} (COL.shiftL :[F2]:))) as H18. {
            rewrite H17, SumOfClass.ShiftL, SumOfClass.ShiftL,
            ToFun.Eval, ToFun.Eval in H15; try assumption.
            - apply ToFun.IsFunctional.
            - intros i H18. apply ToFun.DomainOf.
            - intros i H18. rewrite ToFun.Eval. apply G5.
              rewrite H17. assumption.
            - apply ToFun.IsFunctional.
            - intros i H18. apply ToFun.DomainOf.
            - intros i H18. rewrite ToFun.Eval. apply G6. assumption. }
        clear H15.
        remember (SOL.shiftL c) as c' eqn:H19.
        remember (SOL.shiftL d) as d' eqn:H20.
        remember (SOL.shiftL e) as e' eqn:H21.
        remember (SOL.shiftL f) as f' eqn:H22.
        remember (fun i => a :^: d'!i :*: c'!i) as F1' eqn:E1'.
        remember (fun i => a :^: f'!i :*: e'!i) as F2' eqn:E2'.
        assert (:sum:_{n} (COS.shiftL :[F1]:) = :sum:_{n} :[F1']:) as H23. {
          apply SumOfClass.EqualCharac. 1: assumption. intros i H23.
          assert (Ordinal i) as G16. { apply Core.IsOrdinal with n; assumption. }
          rewrite COL.Eval, ToFun.Eval, ToFun.Eval, E1, E1', H19, H20,
            SOL.Eval, SOL.Eval; try assumption. 1: reflexivity.
          - rewrite G11. apply Succ.ElemCompat; assumption.
          - rewrite G12. apply Succ.ElemCompat; assumption.
          - apply ToFun.IsFunctional.
          - apply ToFun.DomainOf. }
        assert (:sum:_{k} (COS.shiftL :[F2]:) = :sum:_{k} :[F2']:) as H24. {
          apply SumOfClass.EqualCharac. 1: assumption. intros i H24.
          assert (Ordinal i) as G16. { apply Core.IsOrdinal with k; assumption. }
          rewrite COL.Eval, ToFun.Eval, ToFun.Eval, E2, E2', H21, H22,
            SOL.Eval, SOL.Eval; try assumption. 1: reflexivity.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption.
          - rewrite G14, H17. apply Succ.ElemCompat; assumption.
          - apply ToFun.IsFunctional.
          - apply ToFun.DomainOf. }
        rewrite H23, H24 in H18. clear H23 H24.
        assert (Ordinal d!:0:) as G16. {
          apply OrdFunOn.IsOrdinal with (succ n). 1: assumption.
          apply Succ.HasZero. assumption. }
        assert (Ordinal f!:0:) as G17. {
          apply OrdFunOn.IsOrdinal with m. 1: assumption.
          rewrite H17. apply Succ.HasZero. assumption. }
        assert (OrdFunOn c' n) as G18. {
          rewrite H19. apply SOL.OnSucc. assumption. }
        assert (OrdFunOn d' n) as G19. {
          rewrite H20. apply SOL.OnSucc. assumption. }
        assert (OrdFunOn e' k) as G20. {
          rewrite H21. apply SOL.OnSucc. rewrite <- H17. assumption. }
        assert (OrdFunOn f' k) as G21. {
          rewrite H22. apply SOL.OnSucc. rewrite <- H17. assumption. }
        assert (Decreasing d') as G22. {
          rewrite H20. apply SOL.IsDecreasing. 2: assumption. apply H6. }
        assert (Decreasing f') as G23. {
          rewrite H22. apply SOL.IsDecreasing. 2: assumption. apply H8. }
        assert (forall i, i :< n -> c'!i :< a) as G24. {
          rewrite H19. intros i G24.
          assert (Ordinal i) as G25. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H12. apply Succ.ElemCompat; assumption.
          - rewrite G11. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> e'!i :< a) as G25. {
          rewrite H21. intros i G25.
          assert (Ordinal i) as G26. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H14. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< n -> d'!i :< d!:0:) as G26. {
          rewrite H20. intros i G26.
          assert (Ordinal i) as G27. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H9.
            + rewrite G12. apply Succ.HasZero. assumption.
            + rewrite G12. apply Succ.ElemCompat; assumption.
            + apply Succ.HasZero. assumption.
          - rewrite G12. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> f'!i :< f!:0:) as G27. {
          rewrite H22. intros i G27.
          assert (Ordinal i) as G28. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H10.
            + rewrite G14, H17. apply Succ.HasZero. assumption.
            + rewrite G14, H17. apply Succ.ElemCompat; assumption.
            + apply Succ.HasZero. assumption.
          - rewrite G14, H17. apply Succ.ElemCompat; assumption. }
        assert ((:sum:_{n} :[F1']:) :< a :^: d!:0:) as H23. {
          rewrite E1'. apply IsLess; assumption. }
        assert ((:sum:_{k} :[F2']:) :< a :^: f!:0:) as H24. {
          rewrite E2'. apply IsLess; assumption. }
        assert (forall i, i :< succ n -> Ordinal c!i) as G29. {
          intros i G29. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (forall i, i :< m -> Ordinal e!i) as G30. {
          intros i G30. apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< succ n -> Ordinal d!i) as G31. {
          intros i G31. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
        assert (forall i, i :< m -> Ordinal f!i) as G32. {
          intros i G32. apply OrdFunOn.IsOrdinal with m; assumption. }
        assert (forall i, i :< n -> Ordinal c'!i) as G33. {
          rewrite H19. intros i G33.
          assert (Ordinal i) as G34. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G29. apply Succ.ElemCompat; assumption.
          - rewrite G11. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< n -> Ordinal d'!i) as G34. {
          rewrite H20. intros i G34.
          assert (Ordinal i) as G35. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G31. apply Succ.ElemCompat; assumption.
          - rewrite G12. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> Ordinal e'!i) as G35. {
          rewrite H21. intros i G35.
          assert (Ordinal i) as G36. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G30. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> Ordinal f'!i) as G36. {
          rewrite H22. intros i G36.
          assert (Ordinal i) as G37. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply G32. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G14, H17. apply Succ.ElemCompat; assumption. }
        assert (Ordinal (:sum:_{n} :[F1']:)) as G37. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G37. rewrite ToFun.Eval, E1'.
          apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption. apply G34. assumption.
          - apply G33. assumption. }
        assert (Ordinal (:sum:_{k} :[F2']:)) as G38. {
          apply SumOfClass.IsOrdinal. 1: assumption.
          intros i G38. rewrite ToFun.Eval, E2'.
          apply Mult.IsOrdinal.
          - apply IsOrdinal. 1: assumption. apply G36. assumption.
          - apply G35. assumption. }
        assert (Ordinal c!:0:) as G39. {
          apply OrdFunOn.IsOrdinal with (succ n). 1: assumption.
          apply Succ.HasZero. assumption. }
        assert (Ordinal e!:0:) as G40. {
          apply OrdFunOn.IsOrdinal with m. 1: assumption.
          rewrite H17. apply Succ.HasZero. assumption. }
        remember (:sum:_{n} :[F1']:) as r1 eqn:H25.
        remember (:sum:_{k} :[F2']:) as r2 eqn:H26.
        rewrite E1, E2 in H18.
        remember (a :^: d!:0: :*: c!:0: :+: r1) as s1 eqn:H27.
        remember (a :^: f!:0: :*: e!:0: :+: r2) as s2 eqn:H28.
        assert (d!:0: = f!:0:) as H29. {
          assert (d!:0: = f!:0: \/ d!:0: :< f!:0: \/ f!:0: :< d!:0:) as H29. {
            apply Core.IsTotal; assumption. }
          destruct H29 as [H29|[H29|H29]]. 1: assumption.
          - exfalso.
            assert (s1 :< s2) as H30. {
            rewrite H27, H28. apply ExponentFirst; try assumption.
            + apply H12, Succ.HasZero. assumption.
            + apply H13. rewrite H17. apply Succ.HasZero. assumption. }
            assert (s2 :< s2) as H31. { rewrite H18 in H30. assumption. }
            revert H31. apply NoElemLoop1.
          - exfalso.
            assert (s2 :< s1) as H30. {
            rewrite H27, H28. apply ExponentFirst; try assumption.
            + apply H14. rewrite H17. apply Succ.HasZero. assumption.
            + apply H11, Succ.HasZero. assumption. }
            assert (s2 :< s2) as H31. { rewrite H18 in H30. assumption. }
            revert H31. apply NoElemLoop1. }
        assert (c!:0: = e!:0: /\ r1 = r2) as H30. {
          apply Mult.EuclidUnique with (a :^: f!:0:); try assumption.
          - apply IsOrdinal; assumption.
          - rewrite <- H29. assumption.
          - rewrite H27, H28, H29 in H18. assumption. }
        destruct H30 as [H30 H31].
        assert (forall i, i :< n -> :0: :< c'!i) as G41. {
          rewrite H19. intros i G41.
          assert (Ordinal i) as G42. { apply Core.IsOrdinal with n; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H11. apply Succ.ElemCompat; assumption.
          - rewrite G11. apply Succ.ElemCompat; assumption. }
        assert (forall i, i :< k -> :0: :< e'!i) as G42. {
          rewrite H21. intros i G42.
          assert (Ordinal i) as G43. { apply Core.IsOrdinal with k; assumption. }
          rewrite SOL.Eval. 2: assumption.
          - apply H13. rewrite H17. apply Succ.ElemCompat; assumption.
          - rewrite G13, H17. apply Succ.ElemCompat; assumption. }
        assert (n = k /\ c' = e' /\ d' = f') as H32. {
          apply IH; try assumption.
          rewrite H25, H26, E1', E2' in H31. assumption. }
        destruct H32 as [H32 [H33 H34]].
        assert (succ n = m) as H35. { rewrite H32. symmetry. assumption. }
        assert (c = e) as H36. {
          apply SOL.IsEqual with n; try assumption.
          - rewrite <- H35 in H7. assumption.
          - rewrite H19, H21 in H33. assumption. }
        assert (d = f) as H37. {
          apply SOL.IsEqual with n; try assumption.
          - rewrite <- H35 in H8. assumption.
          - rewrite H20, H22 in H34. assumption. }
        split. 1: assumption. split; assumption. }
  rewrite E in H3. assumption.
Qed.

Proposition SumReduceNonNatR : forall (a d n b c:U),
  Ordinal a                                                       ->
  Ordinal d                                                       ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn c (succ n)                                             ->
  :1: :< a                                                        ->
  Decreasing b                                                    ->
  (forall i, i :< succ n -> :0: :< c!i)                           ->
  (forall i, i :< succ n -> c!i :< a )                            ->
  :N :<=: d                                                       ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: c!i]:) :*: a :^: d =
  a :^: (b!:0: :+: d).
Proof.
  intros a d n b c H1 H2 H3 H4 H5 Ha H6 H7 H8 H9.
  remember (fun i => a :^: b!i :*: c!i) as F eqn:H10.
  remember (:sum:_{succ n} :[F]:) as s eqn:H11.
  assert (forall i, i :< succ n -> Ordinal b!i) as G1. {
    intros i G1. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal c!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  assert (succ n :< :N) as G4. { apply Omega.HasSucc. assumption. }
  assert (:0: :< succ n) as G5. { apply Omega.SuccHasZero. assumption. }
  assert (forall i, i :< succ n -> Ordinal (:[F]:!i)) as G6. {
    intros i G6. rewrite ToFun.Eval, H10.
    apply Mult.IsOrdinal.
    - apply IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption. }
  assert (domain b = succ n) as G7. { apply H4. }
  assert (domain c = succ n) as G8. { apply H5. }
  assert (Ordinal (a :^: d)) as G9. { apply IsOrdinal; assumption. }
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H11. apply SumOfClass.IsOrdinal. 1: assumption.
    intros i G11. apply G6. assumption. }
  assert (Ordinal b!:0:) as G12. { apply G1. assumption. }
  assert (Ordinal (succ b!:0:)) as G13. {
    apply Succ.IsOrdinal. apply G1. assumption. }
  assert (:1: :< :N) as G14. { apply Omega.HasOne. }
  assert (Ordinal :1:) as G15. { apply Natural.OneIsOrdinal. }
  assert (a :^: b!:0: :<=: a :^: b!:0: :*: c!:0:) as H12. {
    apply Mult.IsInclR.
    - apply IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption.
    - apply H7. assumption. }
  assert (a :^: b!:0: :<=: s) as H13. {
    apply Incl.Tran with (a :^: b!:0: :*: c!:0:). 1: assumption.
    assert (:[F]:!:0: :<=: :sum:_{succ n} :[F]:) as H13. {
      apply SumOfClass.IsIncl; try assumption.
      intros i H13. apply ToFun.DomainOf. }
    rewrite ToFun.Eval, H10 in H13. rewrite H11, H10. assumption. }
  assert (s :< a :^: succ b!:0:) as H14. {
    rewrite H11, H10. apply IsLess; try assumption.
    intros i H14.
    assert (i :< :N) as K1. { apply Omega.IsIn with (succ n); assumption. }
    assert (i = :0: \/ :0: :< i) as H15. { apply Omega.ZeroOrElem. assumption. }
    destruct H15 as [H15|H15].
    - subst. apply Succ.IsIn.
    - apply ElemElemTran with b!:0:.
      + apply G1. assumption.
      + apply G1. assumption.
      + apply Succ.IsOrdinal, G1. assumption.
      + apply H6; try assumption; rewrite G7; assumption.
      + apply Succ.IsIn. }
  assert (s :*: a :^: d :<=: a :^: (succ b!:0: :+: d)) as H15. {
    rewrite DistribL; try assumption.
    apply Mult.InclCompatL; try assumption.
    - apply IsOrdinal; assumption.
    - apply Core.ElemIsIncl. 2: assumption. apply IsOrdinal; assumption. }
  assert (s :*: a :^: d :<=: a :^: (b!:0: :+: d)) as H16. {
    rewrite <- Plus.WhenOneR, Plus.Assoc, (Plus.WhenNatL :1: d) in H15;
    assumption. }
  assert (a :^: (b!:0: :+: d) :<=: s :*: a :^: d) as H17. {
    rewrite DistribL; try assumption.
    apply Mult.InclCompatL; try assumption.
    apply IsOrdinal; assumption. }
  apply Incl.DoubleInclusion. split; assumption.
Qed.

Proposition SumReduceLimitL : forall (a d n b c:U),
  Limit a                                                         ->
  Ordinal d                                                       ->
  n :< :N                                                         ->
  OrdFunOn b (succ n)                                             ->
  OrdFunOn c (succ n)                                             ->
  Decreasing b                                                    ->
  :0: :< c!:0:                                                    ->
  (forall i, i :< succ n -> c!i :< :N)                            ->
  :0: :< d                                                        ->
  (:sum:_{succ n} :[fun i => a :^: b!i :*: c!i]:) :*: a :^: d =
  a :^: (b!:0: :+: d).
Proof.
  intros a d n b c H1 H2 H3 H4 H5 H6 H7 H8 h9.
  remember (fun i => a :^: b!i :*: c!i) as F eqn:H10.
  remember (:sum:_{succ n} :[F]:) as s eqn:H11.
  assert (Ordinal a) as G0. { apply H1. }
  assert (forall i, i :< succ n -> Ordinal b!i) as G1. {
    intros i G1. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (forall i, i :< succ n -> Ordinal c!i) as G2. {
    intros i G2. apply OrdFunOn.IsOrdinal with (succ n); assumption. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  assert (succ n :< :N) as G4. { apply Omega.HasSucc. assumption. }
  assert (:0: :< succ n) as G5. { apply Omega.SuccHasZero. assumption. }
  assert (forall i, i :< succ n -> Ordinal (:[F]:!i)) as G6. {
    intros i G6. rewrite ToFun.Eval, H10.
    apply Mult.IsOrdinal.
    - apply IsOrdinal. 1: assumption. apply G1. assumption.
    - apply G2. assumption. }
  assert (domain b = succ n) as G7. { apply H4. }
  assert (domain c = succ n) as G8. { apply H5. }
  assert (Ordinal (a :^: d)) as G9. { apply IsOrdinal; assumption. }
  assert (Ordinal (succ n)) as G10. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal s) as G11. {
    rewrite H11. apply SumOfClass.IsOrdinal. 1: assumption.
    intros i G11. apply G6. assumption. }
  assert (Ordinal b!:0:) as G12. { apply G1. assumption. }
  assert (Ordinal (succ b!:0:)) as G13. {
    apply Succ.IsOrdinal. apply G1. assumption. }
  assert (:1: :< :N) as G14. { apply Omega.HasOne. }
  assert (Ordinal :1:) as G15. { apply Natural.OneIsOrdinal. }
  remember (shiftL b) as b' eqn:H12.
  remember (shiftL c) as c' eqn:H13.
  remember (fun i => a :^: b'!i :*: c'!i) as F' eqn:H14.
  assert (OrdFunOn b' n) as G16. { rewrite H12. apply SOL.OnSucc. assumption. }
  assert (OrdFunOn c' n) as G17. { rewrite H13. apply SOL.OnSucc. assumption. }
  assert (Decreasing b') as G18. {
    rewrite H12. apply SOL.IsDecreasing. 2: assumption. apply H4. }
  assert (:1: :< a) as G19. { apply Limit.HasOne. assumption. }
  assert (forall i, i :< n -> c'!i :< a) as G20. {
    intros i G20.
    assert (Ordinal i) as K1. { apply Core.IsOrdinal with n; assumption. }
    apply Omega.InLimitIncl. 1: assumption.
    rewrite H13, SOL.Eval.
    - apply H8. apply Succ.ElemCompat; assumption.
    - apply H5.
    - rewrite G8. apply Succ.ElemCompat; assumption. }
  assert (forall i, i :< n -> b'!i :< b!:0:) as G21. {
    intros i G21.
    assert (Ordinal i) as K1. { apply Core.IsOrdinal with n; assumption. }
    rewrite H12, SOL.Eval.
    - apply H6.
      + rewrite G7. apply Succ.HasZero. assumption.
      + rewrite G7. apply Succ.ElemCompat; assumption.
      + apply Succ.HasZero. assumption.
    - apply H4.
    - rewrite G7. apply Succ.ElemCompat; assumption. }
  remember (:sum:_{n} :[F']:) as s' eqn:H15.
  assert (forall i, i :< n -> Ordinal b'!i) as G22. {
    intros i G22. apply OrdFunOn.IsOrdinal with n; assumption. }
  assert (forall i, i :< n -> Ordinal c'!i) as G23. {
    intros i G23. apply OrdFunOn.IsOrdinal with n; assumption. }
  assert (forall i, i :< n -> Ordinal (:[F']:!i)) as G24. {
    intros i G24. rewrite ToFun.Eval, H14.
    apply Mult.IsOrdinal.
    - apply IsOrdinal. 1: assumption. apply G22. assumption.
    - apply G23. assumption. }
  assert (Ordinal s') as G25. {
    rewrite H15. apply SumOfClass.IsOrdinal; assumption. }
  assert (Ordinal (F :0:)) as G26. {
    rewrite H10. apply Mult.IsOrdinal.
    - apply IsOrdinal; assumption.
    - apply G2. assumption. }
  assert (Ordinal c!:0:) as G27. { apply G2. assumption. }
  assert (Ordinal (a :^: b!:0:)) as G28. { apply IsOrdinal; assumption. }

  assert (s = :[F]:!:0: :+: :sum:_{n} (COL.shiftL :[F]:)) as H16. {
    rewrite H11. apply SumOfClass.ShiftL; try assumption.
    - apply ToFun.IsFunctional.
    - intros i H16. apply ToFun.DomainOf. }
  rewrite ToFun.Eval in H16.
  assert (s' = :sum:_{n} (COL.shiftL :[F]:)) as H17. {
    rewrite H15. apply SumOfClass.EqualCharac. 1: assumption.
    intros i H17.
    assert (Ordinal i) as K1. { apply Core.IsOrdinal with n; assumption. }
    rewrite ToFun.Eval, COL.Eval, ToFun.Eval,
    H14, H10, H12, H13, SOL.Eval, SOL.Eval. 1: reflexivity.
    - apply H5.
    - rewrite G8. apply Succ.ElemCompat; assumption.
    - apply H4.
    - rewrite G7. apply Succ.ElemCompat; assumption.
    - apply ToFun.IsFunctional.
    - apply ToFun.DomainOf. }
  assert (s = F :0: :+: s') as H18. { rewrite H17. assumption. }
  assert (s' :< a :^: b!:0:) as H19. {
    rewrite H15, H14. apply IsLess; assumption. }
  assert (a :^: b!:0: :<=: a :^: b!:0: :*: c!:0:) as H20. {
    apply Mult.IsInclR. 3: assumption.
    - apply IsOrdinal; assumption.
    - apply G2. assumption. }
  assert (a :^: b!:0: :<=: s) as H21. {
    apply Incl.Tran with  (F :0:).
    - rewrite H10. assumption.
    - rewrite H18. apply Plus.IsInclR; assumption. }
  assert (s :< F :0: :+: a :^: b!:0:) as H22. {
    rewrite H18. apply Plus.ElemCompatR; assumption. }
  assert (s :< a :^: b!:0: :*: succ c!:0:) as H23. {
    rewrite H10 in H22.
    rewrite <- Plus.WhenOneR, Mult.DistribL, Mult.WhenOneR; assumption. }
  assert (a :^: (b!:0: :+: d) :<=: s :*: a :^: d) as H24. {
    rewrite DistribL; try assumption.
    apply Mult.InclCompatL; assumption. }
  assert (s :*: a :^: d :<=: a :^: b!:0: :*: succ c!:0: :*: a :^: d) as H25. {
    apply Mult.InclCompatL; try assumption.
    - apply Mult.IsOrdinal. 1: assumption. apply Succ.IsOrdinal. assumption.
    - apply Core.ElemIsIncl. 2: assumption.
      apply Mult.IsOrdinal. 1: assumption. apply Succ.IsOrdinal. assumption. }
  assert (s :*: a :^: d :<=: a :^: b!:0: :*: a :^: d) as H26. {
    rewrite Mult.Assoc, (Mult.LimitWithNatSimple (succ c!:0:)) in H25;
    try assumption.
    - apply Omega.HasSucc, H8, Succ.HasZero. assumption.
    - apply IsLimitL; assumption.
    - apply Succ.HasZero. assumption.
    - apply Succ.IsOrdinal. assumption. }
  assert (s :*: a :^: d :<=: a :^: (b!:0: :+: d)) as H27. {
    rewrite DistribL; assumption. }
  apply Incl.DoubleInclusion. split; assumption.
Qed.



