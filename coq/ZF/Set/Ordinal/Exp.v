Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Exp.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Exp.
Export ZF.Notation.Exp.

Module COE := ZF.Class.Ordinal.Exp.
Module SOG := ZF.Set.Ordinal.UnionGenOfClass.

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
  apply COE.WhenLimit. 1: assumption. apply Empty.HasElem.
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
  apply Induction2.
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
  apply Induction2.
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

Proposition OneIsIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  :1: :<=: a -> :1: :<=: a :^: b.
Proof.
  intros a b H1. revert b.
  assert (Ordinal :1:) as G1. { apply Natural.OneIsOrdinal. }
  assert (Ordinal :0:) as G2. { apply Core.ZeroIsOrdinal. }
  remember (fun b => :1: :<=: a -> :1: :<=: a :^: b) as A eqn:H2.
  assert (forall b, Ordinal b -> A b) as X. 2: { rewrite H2 in X. assumption. }
  apply Induction2; rewrite H2.
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
  - apply Core.InclIsEqualOrElem in H5; try assumption.
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
  apply Induction2.
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
    apply Empty.HasElem. exists a. assumption.
Qed.
