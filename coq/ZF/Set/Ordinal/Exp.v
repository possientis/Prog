Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Exp.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
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
  assert (a = succ :U(a) \/ Limit a) as H3. { apply Limit.TwoWay; assumption. }
  destruct H3 as [H3|H3].
  - rewrite H3, WhenSuccR, Mult.WhenZeroR. 1: reflexivity.
    apply UnionOf.IsOrdinal. assumption.
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
