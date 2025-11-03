Require Import ZF.Class.Empty.
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
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Plus.
Export ZF.Notation.Plus.

Module COP := ZF.Class.Ordinal.Plus.
Module SOO := ZF.Set.Ordinal.UnionOf.
Module SOG := ZF.Set.Ordinal.UnionGenOfClass.
Module SUG := ZF.Set.UnionGenOfClass.

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
    apply SOG.IsOrdinal. intros c H4. apply H3. assumption.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :+: a = a.
Proof.
  apply Induction2.
  - apply WhenZeroR.
  - intros a H1 H2. rewrite WhenSucc. 2: assumption. rewrite H2. reflexivity.
  - intros a H1 H2. rewrite WhenLimit. 2: assumption.
    rewrite <- SOG.WhenLimit. 2: assumption.
    apply SUG.EqualCharac. intros x. rewrite I.Eval. apply H2.
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
  - rewrite WhenSucc. 2: assumption. apply Succ.IsIn.
  - intros b H6 H7 H8. rewrite WhenSucc. 2: assumption.
    assert (Ordinal (c :+: a)) as H9.  { apply IsOrdinal; assumption. }
    assert (Ordinal (c :+: b)) as H10. { apply IsOrdinal; assumption. }
    apply ElemElemTran with (c :+: b); try assumption.
    + apply Succ.IsOrdinal. assumption.
    + apply Succ.IsIn.
  - intros b H6 H7 H8. rewrite (WhenLimit c b). 2: assumption.
    apply Limit.InclIsElem in H7; try assumption.
    apply SUG.Charac. exists (succ a). split. 1: assumption.
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
    apply SUG.InclCompatR. assumption.
Qed.

Proposition InclCompatR : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  a :<=: b                ->
  c :+: a :<=: c :+: b.
Proof.
  intros a b c H1 H2 H3. revert b H2.
  apply Induction2'. 1: assumption.
  - apply Incl.Refl.
  - intros b H4 H5 H6.
    rewrite WhenSucc. 2: assumption.
    apply Incl.Tran with (c :+: b). 1: assumption.
    apply Succ.IsIncl.
  - intros b H4 H5 H6.
    rewrite  (WhenLimit c b). 2: assumption.
    intros x H7. apply SUG.Charac.
Admitted.

(* ERROR: see page 59 proposition 8.8. Typo in big union: 'delta <  beta'       *)
(* should be 'delta < gamma'.                                                   *)
Proposition CompleteR : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b -> exists c, Ordinal c /\ a :+: c = b.
Proof.
  intros a b H1 H2 H3.
  remember (fun c => Ordinal c /\ b :<=: a :+: c) as A eqn:H4.
  assert (A :<=: Ordinal) as H5. { intros c H5. rewrite H4 in H5. apply H5. }
  assert (A :<>: :0:) as H6. {
    apply Class.Empty.HasElem. exists b. rewrite H4. split. 1: assumption.
    assert (:0: :+: b :<=: a :+: b) as H6. {
      apply InclCompatL; try assumption.
      - apply Natural.ZeroIsOrdinal.
      - intros x H6. apply Empty.Charac in H6. contradiction. }
    rewrite WhenZeroL in H6. 2: assumption. assumption. }
  assert (exists c, Ordinal c /\ A c /\ forall d, A d -> c :<=: d) as H7. {
    apply Core.HasMinimal; assumption. }
  destruct H7 as [c [H7 [H8 H9]]].
  rewrite H4 in H8. destruct H8 as [_ H8]. rewrite H4 in H9.
  exists c. split. 1: assumption. apply DoubleInclusion. split. 2: assumption.
  assert (c = :0: \/ c = succ :U(c) \/ Limit c) as H10. {
    apply Limit.ThreeWay. assumption. }
  assert (forall d, Ordinal d -> d :< c -> a :+: d :< b) as G1. {
    intros d H11 H12.
    assert (Ordinal (a :+: d)) as H13. { apply IsOrdinal; assumption. }
    assert (a :+: d :< b \/ b :<=: a :+: d) as H14. {
      apply Core.ElemOrIncl; assumption. }
    destruct H14 as [H14|H14]. 1: assumption.
    exfalso. apply NoElemLoop1 with d. apply H9. 2: assumption.
    split; assumption. }
  destruct H10 as [H10|[H10|H10]].
  - rewrite H10. rewrite WhenZeroR. assumption.
  - remember (:U(c)) as d eqn:H11.
    assert (Ordinal d) as H12. { rewrite H11. apply SOO.IsOrdinal. assumption. }
    assert (Ordinal (a :+: d)) as H13. { apply IsOrdinal; assumption. }
    assert (a :+: d :< b) as H14. {
      apply G1. 1: assumption. rewrite H10. apply Succ.IsIn. }
    apply ElemIsIncl in H14; try assumption. rewrite H10.
    rewrite WhenSucc; assumption.
  - rewrite WhenLimit. 2: assumption. apply SUG.WhenBounded.
    intros d H15.
    assert (Ordinal d) as H16. { apply Core.IsOrdinal with c; assumption. }
    assert (Ordinal (a :+: d)) as H17. { apply IsOrdinal; assumption. }
    apply Core.ElemIsIncl. 1: assumption. apply G1; assumption.
Qed.

Proposition InOmega : forall (n m:U),
  n :< :N -> m :< :N -> n :+: m :< :N.
Proof.
  intros n m H1. revert m. apply FiniteInduction'.
  - rewrite WhenZeroR. assumption.
  - intros m H2 H3.
    assert (Ordinal n) as H4. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal m) as H5. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal (n :+: m)) as H6. { apply IsOrdinal; assumption. }
    rewrite WhenSucc. 2: assumption. apply Omega.HasSucc. assumption.
Qed.

Proposition InOmegaL : forall (n m:U), Ordinal n -> Ordinal m ->
  n :+: m :< :N -> n :< :N.
Proof.
  intros n m H1 H2 H3.
  apply Core.InclElemTran with (n :+: m); try assumption.
  - apply IsOrdinal; assumption.
  - apply Omega.IsOrdinal.
  - assert (n :+: :0: :<=: n :+: m) as H4. {
Admitted.

Proposition WhenNaturalL : forall (n a:U), Ordinal a ->
  n :< :N -> :N :<=: a -> n :+: a = a.
Proof.
  intros n a H1 H2. revert a H1.
  apply Induction2'.
  - apply Omega.IsOrdinal.
  - apply DoubleInclusion. split.
    + rewrite WhenLimit. 2: apply Omega.IsLimit.
      apply SUG.WhenBounded. intros m H1.
      apply Core.ElemIsIncl. 1: apply Omega.IsOrdinal.
      apply InOmega; assumption.
    + rewrite WhenLimit. 2: apply Omega.IsLimit. intros m H1. apply SUG.Charac.
      assert (Ordinal n) as H3. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal m) as H4. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal (succ m)) as H5. { apply Succ.IsOrdinal. assumption. }
      assert (succ m :< n \/ n :<=: succ m) as H6. {
        apply Core.ElemOrIncl; assumption. }
      destruct H6 as [H6|H6].
      * exists :0:. split. 1: apply Omega.HasZero.
        assert (m :< n :+: :0:) as X. 2: apply X. rewrite WhenZeroR.
        apply Core.ElemElemTran with (succ m); try assumption.
        apply Succ.IsIn.
      * assert (exists p, Ordinal p /\ n :+: p = succ m) as H7. {
          apply CompleteR; assumption. }
        destruct H7 as [p [H7 H8]]. exists p.
        assert (p :< :N) as H9. {
          apply Core.InclElemTran with (succ m); try assumption.
          - apply Omega.IsOrdinal.
          Admitted.
