Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Plus.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Plus.
Export ZF.Notation.Plus.

Module COP := ZF.Class.Ordinal.Plus.
Module SOU := ZF.Set.Ordinal.UnionGenOfClass.
Module SUC := ZF.Set.UnionGenOfClass.

(* The sum of two ordinals when a is an ordinal.                                *)
Definition plus (a b:U) : U := (COP.Plus a)!b.

(* Notation "a :+: b" := ((plus a)!b)                                           *)
Global Instance SetPlus : Plus U := { plus := plus }.

Proposition WhenZeroR : forall (a:U), a :+: :0: = a.
Proof.
  apply COP.WhenZero.
Qed.

Proposition WhenOneR : forall (a:U), a :+: :1: = succ a.
Proof.
  intros a.
  assert (a :+: :1: = succ (a :+: :0:)) as H1. {
    apply COP.WhenSucc, Natural.ZeroIsOrdinal. }
  rewrite H1. rewrite WhenZeroR. reflexivity.
Qed.

Proposition WhenSucc : forall (a b:U), Ordinal b ->
  a :+: (succ b) = succ (a :+: b).
Proof.
  apply COP.WhenSucc.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  a :+: b = :\/:_{b} (COP.Plus a).
Proof.
  apply COP.WhenLimit.
Qed.

Proposition IsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :+: b).
Proof.
  intros a b H1. revert b. apply Induction2.
  - rewrite WhenZeroR. assumption.
  - intros b H2 H3. rewrite WhenSucc. 2: assumption.
    apply Succ.IsOrdinal. assumption.
  - intros b H2 H3. rewrite WhenLimit. 2: assumption.
    apply SOU.IsOrdinal. intros c H4. apply H3. assumption.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :+: a = a.
Proof.
  apply Induction2.
  - apply WhenZeroR.
  - intros a H1 H2. rewrite WhenSucc. 2: assumption. rewrite H2. reflexivity.
  - intros a H1 H2. rewrite WhenLimit. 2: assumption.
    rewrite <- SOU.WhenLimit. 2: assumption.
    apply SUC.EqualCharac. intros x. rewrite I.Eval. apply H2.
Qed.

(* ERROR: See page 58, proposition 8.4. Proof is wrong in my opinion.           *)
(* Unless you know that alpha < beta (so there is a delta in between), the last *)
(* step of the proof cannot be justified.                                       *)
Proposition ElemCompatR : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  a :< b                ->
  c :+: a :< c :+: b.
Proof.
  intros a b c H1 H2 H3 H4. apply Succ.ElemIsIncl in H4; try assumption.
  assert (Ordinal (succ a)) as H5. { apply Succ.IsOrdinal. assumption. }
  revert b H2 H4.
  apply Induction2'. 1: assumption.
  - apply Succ.HasZero. assumption.
  - rewrite WhenSucc. 2: assumption. apply Succ.IsIn.
  - intros b H6 H7 H8. rewrite WhenSucc. 2: assumption.
    assert (Ordinal (c :+: a)) as H9.  { apply IsOrdinal; assumption. }
    assert (Ordinal (c :+: b)) as H10. { apply IsOrdinal; assumption. }
    apply ElemElemTran with (c :+: b); try assumption.
    + apply Succ.IsOrdinal. assumption.
    + apply Succ.IsIn.
  - intros b H6 H7 H8. rewrite (WhenLimit c b). 2: assumption.
    apply Limit.InclIsElem in H7; try assumption.
    apply UnionGenOfClass.Charac. exists (succ a). split. 1: assumption.
    apply H8. 2: assumption. apply Incl.Refl.
Qed.

Proposition CancelL : forall (a b c:U),
  Ordinal a           ->
  Ordinal b           ->
  Ordinal c           ->
  c :+: a = c :+: b   ->
  a = b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (Ordinal (c :+: a)) as H5. { apply IsOrdinal; assumption. }
  assert (Ordinal (c :+: b)) as H6. { apply IsOrdinal; assumption. }
  assert (a = b \/ a :< b \/ b :< a) as H7. { apply Core.IsTotal; assumption. }
  destruct H7 as [H7|[H7|H7]]; try assumption; exfalso;
  apply (ElemCompatR _ _ c) in H7; try assumption; rewrite H4 in H7; revert H7;
  apply NoElemLoop1.
Qed.

Proposition InclCompatL : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  a :<=: b                ->
  a :+: c :<=: b :+: c.
Proof.
  intros a b c H1 H2 H3 H4. revert c H3.
  apply Induction2.
  - rewrite WhenZeroR, WhenZeroR. assumption.
  - intros c H5 H6.
    assert (Ordinal (a :+: c)) as H7. { apply IsOrdinal; assumption. }
    assert (Ordinal (b :+: c)) as H8. { apply IsOrdinal; assumption. }
    rewrite WhenSucc. 2: assumption. rewrite WhenSucc. 2: assumption.
    apply Succ.InclCompat; assumption.
  - intros c H5 H6.
    rewrite WhenLimit. 2: assumption. rewrite WhenLimit. 2: assumption.
    intros d H7. apply UnionGenOfClass.Charac in H7.
Admitted.
