Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Order.Le.
Require Import ZF.Class.Ordinal.Plus.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Sup.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Specify.
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

(* Notation "a :+: b" := (plus a b)                                             *)
Global Instance SetPlus : Plus U := { plus := plus }.

Proposition WhenZeroR : forall (a:U), a :+: :0: = a.
Proof.
  apply COP.WhenZero.
Qed.

(* 1 + N = N, so we cannot hope to have a WhenOneL.                             *)
Proposition WhenOneR : forall (a:U), a :+: :1: = succ a.
Proof.
  intros a.
  assert (a :+: :1: = succ (a :+: :0:)) as H1. {
    apply COP.WhenSucc, Core.ZeroIsOrdinal. }
  rewrite H1. rewrite WhenZeroR. reflexivity.
Qed.

Proposition WhenSuccR : forall (a b:U), Ordinal b ->
  a :+: (succ b) = succ (a :+: b).
Proof.
  apply COP.WhenSucc.
Qed.

Proposition WhenSuccL : forall (a n:U), Ordinal a -> n :< :N ->
  succ a :+: n = succ (a :+: n).
Proof.
  intros a n H1. revert n.
  apply Omega.Induction.
  - rewrite WhenZeroR, WhenZeroR. reflexivity.
  - intros n H2 IH.
    assert (Ordinal n) as H3. { apply Omega.HasOrdinalElem.  assumption. }
    rewrite WhenSuccR. 2: assumption. rewrite IH, WhenSuccR.
    2: assumption. reflexivity.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  a :+: b = :\/:_{b} (COP.Plus a).
Proof.
  apply COP.WhenLimit.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :+: a = a.
Proof.
  apply Induction2.Induction.
  - apply WhenZeroR.
  - intros a H1 H2. rewrite WhenSuccR. 2: assumption. rewrite H2. reflexivity.
  - intros a H1 H2. rewrite WhenLimit. 2: assumption.
    rewrite <- SOG.WhenLimit. 2: assumption.
    apply SUG.EqualCharac. intros x. rewrite I.Eval. apply H2.
Qed.

Proposition IsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :+: b).
Proof.
  intros a b H1. revert b. apply Induction2.Induction.
  - rewrite WhenZeroR. assumption.
  - intros b H2 H3. rewrite WhenSuccR. 2: assumption.
    apply Succ.IsOrdinal. assumption.
  - intros b H2 H3. rewrite WhenLimit. 2: assumption.
    apply SOG.IsOrdinal. apply H3.
Qed.

(* Note: 0 + N = 1 + N despite the fact that 0 < 1. So no 'ElemCompatL'         *)
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
  - rewrite WhenSuccR. 2: assumption. apply Succ.IsIn.
  - intros b H6 H7 H8. rewrite WhenSuccR. 2: assumption.
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

Proposition InclCompatRevR : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  c :+: a :<=: c :+: b  ->
  a :<=: b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (b :< a \/ a :<=: b) as H5. { apply Core.ElemOrIncl; assumption. }
  destruct H5 as [H5|H5]. 2: assumption. exfalso.
  assert (c :+: b :< c :+: a) as H6. { apply ElemCompatR; assumption. }
  assert (c :+: b  :< c :+: b) as H7. { apply H4. assumption. }
  revert H7. apply NoElemLoop1.
Qed.

(* Note: 0 + N = 1 + N so we cannot hope to have a 'CancelR'                    *)
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

(* Cancelling a natural number from the right is fine.                          *)
Proposition CancelR : forall (a b n:U),
  Ordinal a           ->
  Ordinal b           ->
  n :< :N             ->
  a :+: n = b :+: n   ->
  a = b.
Proof.
  intros a b n H1 H2. revert n.
  remember (fun n => a :+: n = b :+: n -> a = b) as A eqn:H3.
  assert (forall n, n :< :N -> A n) as H4. {
    apply Omega.Induction; rewrite H3.
    - intros H4. rewrite WhenZeroR, WhenZeroR in H4. assumption.
    - intros n H4 IH H6.
      assert (Ordinal n) as H7. { apply Omega.HasOrdinalElem. assumption. }
      rewrite WhenSuccR, WhenSuccR in H6; try assumption.
      apply Succ.Injective in H6. apply IH. assumption. }
  rewrite H3 in H4. assumption.
Qed.

Proposition InclCompatL : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  a :<=: b                ->
  a :+: c :<=: b :+: c.
Proof.
  intros a b c H1 H2 H3 H4. revert c H3.
  apply Induction2.Induction.
  - rewrite WhenZeroR, WhenZeroR. assumption.
  - intros c H5 H6.
    assert (Ordinal (a :+: c)) as H7. { apply IsOrdinal; assumption. }
    assert (Ordinal (b :+: c)) as H8. { apply IsOrdinal; assumption. }
    rewrite WhenSuccR. 2: assumption. rewrite WhenSuccR. 2: assumption.
    apply Succ.InclCompat; assumption.
  - intros c H5 H6.
    rewrite WhenLimit. 2: assumption. rewrite WhenLimit. 2: assumption.
    apply SUG.InclCompatR. assumption.
Qed.

Proposition ElemCompatRevL : forall (a b c:U),
  Ordinal a           ->
  Ordinal b           ->
  Ordinal c           ->
  a :+: c :< b :+: c  ->
  a :< b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (a :< b \/ b :<=: a) as H5. { apply Core.ElemOrIncl; assumption. }
  destruct H5 as [H5|H5]. 1: assumption. exfalso.
  assert (b :+: c :<=: a :+: c) as H6. { apply InclCompatL; assumption. }
  assert (a :+: c :< a :+: c) as H7. { apply H6. assumption. }
  revert H7. apply NoElemLoop1.
Qed.

Proposition InclCompatR : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  a :<=: b                ->
  c :+: a :<=: c :+: b.
Proof.
  intros a b c H1 H2 H3 H4.
  apply Core.EqualOrElem in H4; try assumption.
  assert (Ordinal (c :+: b)) as G1. { apply IsOrdinal; assumption. }
  destruct H4 as [H4|H4].
  - subst. apply Incl.Refl.
  - apply Core.ElemIsIncl. 1: assumption. apply ElemCompatR; assumption.
Qed.

Proposition InclCompat : forall (a b c d:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  Ordinal d               ->
  a :<=: c                ->
  b :<=: d                ->
  a :+: b :<=: c :+: d.
Proof.
  intros a b c d H1 H2 H3 H4 H5 H6.
  apply Incl.Tran with (c :+: b).
  - apply InclCompatL; assumption.
  - apply InclCompatR; assumption.
Qed.

Proposition ElemCompatRevR : forall (a b c:U),
  Ordinal a          ->
  Ordinal b          ->
  Ordinal c          ->
  c :+: a :< c :+: b ->
  a :< b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (a :< b \/ b :<=: a) as H5. { apply Core.ElemOrIncl; assumption. }
  destruct H5 as [H5|H5]. 1: assumption. exfalso.
  assert (c :+: b :<=: c :+: a) as H6. { apply InclCompatR; assumption. }
  assert (c :+: a :< c :+: a) as H7. { apply H6. assumption. }
  revert H7. apply NoElemLoop1.
Qed.

Proposition IsInclL : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b :+: a.
Proof.
  intros a b H1 H2.
  assert (:0: :+: a :<=: b :+: a) as H3. {
    apply InclCompatL; try assumption.
    - apply Core.ZeroIsOrdinal.
    - apply Core.IsIncl. assumption. }
  rewrite WhenZeroL in H3; assumption.
Qed.

Proposition IsInclR : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: a :+: b.
Proof.
  intros a b H1 H2.
  assert (a :+: :0: :<=: a :+: b) as H3. {
    apply InclCompatR; try assumption.
    - apply Core.ZeroIsOrdinal.
    - apply Core.IsIncl. assumption. }
  rewrite WhenZeroR in H3. assumption.
Qed.

Proposition IsElemAddR : forall (a b:U), Ordinal a -> Ordinal b ->
  b <> :0: -> a :< a :+: b.
Proof.
  intros a b H1 H2 H3.
  assert (:0: :< b) as H4. { apply Core.HasZero; assumption. }
  assert (a :+: :0: :< a :+: b) as H5. {
    apply ElemCompatR; try assumption. apply Core.ZeroIsOrdinal. }
  rewrite WhenZeroR in H5. assumption.
Qed.

Proposition WhenZero : forall (a b:U), Ordinal a -> Ordinal b ->
  a :+: b = :0: -> a = :0: /\ b = :0:.
Proof.
  intros a b H1 H2 H3. split.
  - assert (a :<=: :0:) as H4. {
      apply Incl.Tran with (a :+: b).
      - apply IsInclR; assumption.
      - rewrite H3. apply Incl.Refl. }
    apply DoubleInclusion. split. 1: assumption.
    apply Core.IsIncl. assumption.
  - assert (b :<=: :0:) as H4. {
      apply Incl.Tran with (a :+: b).
      - apply IsInclL; assumption.
      - rewrite H3. apply Incl.Refl. }
    apply DoubleInclusion. split. 1: assumption.
    apply Core.IsIncl. assumption.
Qed.

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
      - apply Core.ZeroIsOrdinal.
      - intros x H6. apply Empty.Charac in H6. contradiction. }
    rewrite WhenZeroL in H6. 2: assumption. assumption. }
  assert (exists c, Ordinal c /\ A c /\ forall d, A d -> c :<=: d) as H7. {
    apply Core.HasMinimal; assumption. }
  destruct H7 as [c [H7 [H8 H9]]].
  rewrite H4 in H8. destruct H8 as [_ H8]. rewrite H4 in H9.
  exists c. split. 1: assumption. apply DoubleInclusion. split. 2: assumption.
  assert (c = :0: \/ Successor c \/ Limit c) as H10. {
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
  - destruct H10 as [H10 [d H11]].
    assert (Ordinal d) as H12. { apply Succ.IsOrdinalRev. subst. assumption. }
    assert (Ordinal (a :+: d)) as H13. { apply IsOrdinal; assumption. }
    assert (a :+: d :< b) as H14. {
      apply G1. 1: assumption. rewrite H11. apply Succ.IsIn. }
    apply ElemIsIncl in H14; try assumption. rewrite H11.
    rewrite WhenSuccR; assumption.
  - rewrite WhenLimit. 2: assumption. apply SUG.WhenBounded.
    intros d H15.
    assert (Ordinal d) as H16. { apply Core.IsOrdinal with c; assumption. }
    assert (Ordinal (a :+: d)) as H17. { apply IsOrdinal; assumption. }
    apply Core.ElemIsIncl. 1: assumption. apply G1; assumption.
Qed.

Proposition InOmega : forall (n m:U),
  n :< :N -> m :< :N -> n :+: m :< :N.
Proof.
  intros n m H1. revert m. apply Omega.Induction.
  - rewrite WhenZeroR. assumption.
  - intros m H2 H3.
    assert (Ordinal n) as H4. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal m) as H5. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal (n :+: m)) as H6. { apply IsOrdinal; assumption. }
    rewrite WhenSuccR. 2: assumption. apply Omega.HasSucc. assumption.
Qed.

Proposition InOmegaL : forall (n m:U), Ordinal n -> Ordinal m ->
  n :+: m :< :N -> n :< :N.
Proof.
  intros n m H1 H2 H3.
  apply Core.InclElemTran with (n :+: m); try assumption.
  - apply IsOrdinal; assumption.
  - apply Omega.IsOrdinal.
  - assert (n :+: :0: :<=: n :+: m) as H4. {
      apply InclCompatR; try assumption.
      - apply Core.ZeroIsOrdinal.
      - apply Core.IsIncl. assumption. }
    rewrite WhenZeroR in H4. assumption.
Qed.

Proposition InOmegaR : forall (n m:U), Ordinal n -> Ordinal m ->
  n :+: m :< :N -> m :< :N.
Proof.
  intros n m H1 H2 H3.
  apply Core.InclElemTran with (n :+: m); try assumption.
  - apply IsOrdinal; assumption.
  - apply Omega.IsOrdinal.
  - assert (:0: :+: m :<=: n :+: m) as H4. {
      apply InclCompatL; try assumption.
      - apply Core.ZeroIsOrdinal.
      - apply Core.IsIncl. assumption. }
    rewrite WhenZeroL in H4; assumption.
Qed.

Proposition CompleteOmegaR : forall (n m:U), n :< :N -> m :< :N ->
  n :<=: m -> exists p, p :< :N /\ n :+: p = m.
Proof.
  intros n m H1 H2 H3.
  assert (Ordinal n) as H4. { apply Omega.HasOrdinalElem. assumption. }
  assert (Ordinal m) as H5. { apply Omega.HasOrdinalElem. assumption. }
  assert (exists p, Ordinal p /\ n :+: p = m) as H6. {
    apply CompleteR; assumption. }
  destruct H6 as [p [H6 H7]].
  exists p. split. 2: assumption. apply InOmegaR with n; try assumption.
  rewrite H7. assumption.
Qed.

(* Adding a natural number to a non-integer ordinal yields the same ordinal.    *)
Proposition WhenNatL : forall (n a:U), Ordinal a ->
  n :< :N -> :N :<=: a -> n :+: a = a.
Proof.
  intros n a H1 H2. revert a H1.
  assert (Ordinal n) as G4. { apply Omega.HasOrdinalElem. assumption. }
  assert (n :+: :N = :N) as G0. {
    apply DoubleInclusion. split.
    - rewrite WhenLimit. 2: apply Omega.IsLimit.
      apply SUG.WhenBounded. intros m H1.
      apply Core.ElemIsIncl. 1: apply Omega.IsOrdinal.
      apply InOmega; assumption.
    - rewrite WhenLimit. 2: apply Omega.IsLimit. intros m H1. apply SUG.Charac.
      assert (Ordinal m) as H4. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal (succ m)) as H5. { apply Succ.IsOrdinal. assumption. }
      assert (succ m :< n \/ n :<=: succ m) as H6. {
        apply Core.ElemOrIncl; assumption. }
      destruct H6 as [H6|H6].
      + exists :0:. split. 1: apply Omega.HasZero.
        assert (m :< n :+: :0:) as X. 2: apply X. rewrite WhenZeroR.
        apply Core.ElemElemTran with (succ m); try assumption.
        apply Succ.IsIn.
      + assert (exists p, p :< :N /\ n :+: p = succ m) as H7. {
          apply CompleteOmegaR; try assumption.
          apply Omega.HasSucc. assumption. }
        destruct H7 as [p [H7 H8]].
        exists p. split. 1: assumption.
        assert (m :< n :+: p) as X. 2: apply X. (* rewrite failing *)
        rewrite H8. apply Succ.IsIn. }
  apply Induction2'.
  - apply Omega.IsOrdinal.
  - assumption.
  - intros a H1 H3 H4.
    rewrite WhenSuccR. 2: assumption. rewrite H4. reflexivity.
  - intros a H1 H3 H4.
    assert (Ordinal a) as G1. { apply H1. }
    assert (Ordinal :N) as G3. { apply Omega.IsOrdinal. }
    rewrite WhenLimit. 2: assumption. apply DoubleInclusion. split; intros y H5.
    + apply SUG.Charac in H5. destruct H5 as [x [H5 H6]].
      assert (Ordinal x) as H7. { apply Core.IsOrdinal with a; assumption. }
      assert (x :< :N \/ :N :<=: x) as H8. { apply Core.ElemOrIncl; assumption. }
      assert (y :< n :+: x) as G2. { assumption. }
      destruct H8 as [H8|H8].
      * assert (n :+: x :< :N) as H10. { apply InOmega; assumption. }
        assert (Ordinal (n :+: x)) as H11. {
          apply Omega.HasOrdinalElem. assumption. }
        assert (Ordinal y) as H12. {
          apply Core.IsOrdinal with (n :+: x); assumption. }
        apply H3. apply Core.ElemElemTran with (n :+: x); assumption.
      * assert (n :+: x = x) as H10. { apply H4; assumption. }
        rewrite H10 in G2.
        assert (Ordinal y) as H11. { apply Core.IsOrdinal with x; assumption. }
        apply Core.ElemElemTran with x; assumption.
    + assert (Ordinal y) as H16. { apply Core.IsOrdinal with a; assumption. }
      assert (y :< :N \/ :N :<=: y) as H6. { apply Core.ElemOrIncl; assumption. }
      destruct H6 as [H6|H6].
      * rewrite <- WhenLimit. 2: assumption.
        assert (n :+: :N :<=: n :+: a) as H7. { apply InclCompatR; assumption. }
        apply H7. rewrite G0. assumption.
      * apply Limit.InBetween in H5. 2: assumption. destruct H5 as [b [H5 H8]].
        apply SUG.Charac. exists b. split. 1: assumption.
        assert (Ordinal b) as H9. { apply Core.IsOrdinal with a; assumption. }
        assert (y :< n :+: b) as X. 2: apply X. (* rewrite failing *)
        rewrite H4; try assumption. apply Core.ElemIsIncl. 1: assumption.
        apply Core.InclElemTran with y; assumption.
Qed.

Proposition LimitWithNat : forall (a n:U),
  Limit a           ->
  n :< :N           ->
  Limit (a :+: n)   ->
  n = :0:.
Proof.
  intros a n H1 H2 H3.
  assert (Ordinal a) as G1. { apply H1. }
  assert (Ordinal :N) as H4. { apply Omega.IsOrdinal. }
  assert (Ordinal n) as H5. { apply HasOrdinalElem. assumption. }
  assert (n = :0: \/ :0: :< n) as H6. { apply Core.ZeroOrElem. assumption. }
  destruct H6 as [H6|H6]. 1: assumption. exfalso.
  assert (Successor n) as H7. { apply Omega.IsSuccessor; assumption. }
  destruct H7 as [H7 [m H8]].
  assert (Ordinal m) as H9. {
    apply Succ.IsOrdinalRev. rewrite <- H8. assumption. }
  apply Limit.NotBoth with (a :+: n). 1: assumption. right.
  split. 1: apply H3. exists (a :+: m). subst. apply WhenSuccR. assumption.
Qed.

(* The sum of an ordinal and a limit ordinal is a limit ordinal.                *)
Proposition IsLimit : forall (a b:U), Ordinal a ->
  Limit b -> Limit (a :+: b).
Proof.
  intros a b H1 H2.
  assert (Ordinal b) as H3. { apply H2. }
  assert (Ordinal (a :+: b)) as H4. { apply IsOrdinal; assumption. }
  assert (a :+: b <> :0:) as H5. {
    assert (:0: :<=: a) as H5. { apply Core.IsIncl. assumption. }
    assert (Ordinal :0:) as H6. { apply Core.ZeroIsOrdinal. }
    assert (:0: :+: b :<=: a :+: b) as H7. { apply InclCompatL; assumption. }
    assert (b :<=: a :+: b) as H8. { rewrite WhenZeroL in H7; assumption. }
    assert (:0: :< b) as H9. { apply Limit.HasZero. assumption. }
    apply Empty.HasElem. exists :0:. apply H8. assumption. }
  assert (a :+: b <> succ :U(a :+: b)) as H6. {
    remember (:U(a :+: b)) as d eqn:H6.
    assert (a :+: b <> succ d) as X. 2: apply X. (* emphasis only *)
    assert (a :+: b = :\/:_{b} (COP.Plus a)) as H8. {
      apply WhenLimit. assumption. }
    intros H7. (* assume a + b = d + 1, need a contradiction *)
    assert (d :< :\/:_{b} (COP.Plus a)) as H9. {
      rewrite <- H8, H7. apply Succ.IsIn. }
    assert (exists c, Ordinal c /\ c :< b /\ d :< a :+: c) as H10. {
      apply SUG.Charac in H9. destruct H9 as [c [H9 H10]].
      exists c. split.
      - apply Core.IsOrdinal with b; assumption.
      - split; assumption. }
    destruct H10 as [c [H10 [H11 H12]]].
    assert (Ordinal (a :+: c)) as H13. { apply IsOrdinal; assumption. }
    assert (Ordinal d) as H14. {
      apply Core.IsOrdinal with (a :+: c); assumption. }
    assert (succ d :< succ (a :+: c)) as H15. {
      apply Succ.ElemCompat; assumption. }
    assert (succ c :< b) as H16. { apply Limit.HasSucc; assumption. }
    assert (succ d :< :\/:_{b} (COP.Plus a)) as H17. {
      apply SUG.Charac. exists (succ c). split. 1: assumption.
      assert (succ d :< a :+: (succ c)) as X. 2: apply X. (* failing rewrite *)
      rewrite WhenSuccR; assumption. }
    assert (succ d :< succ d) as H18. { (* our contradicton *)
      rewrite <- H8 in H17. rewrite H7 in H17. assumption. }
    revert H18. apply NoElemLoop1. }
  assert (a :+: b = :0: \/ Successor (a :+: b) \/ Limit (a :+: b)) as H7. {
    apply Limit.ThreeWay. assumption. }
  destruct H7 as [H7|[H7|H7]]; try contradiction. 2: assumption.
  exfalso. apply H6. symmetry. apply Succ.OfUnion; assumption.
Qed.

(* The addition of ordinals is associative.                                     *)
Proposition Assoc : forall (a b c:U), Ordinal a -> Ordinal b -> Ordinal c ->
  (a :+: b) :+: c = a :+: (b :+: c).
Proof.
  intros a b c H1 H2. revert c.
  assert ((a :+: b) :+: :0: = a :+: (b :+: :0:)) as H3. {
    rewrite WhenZeroR, WhenZeroR. reflexivity. }
  assert (forall c,
    Ordinal c                                           ->
    (a :+: b) :+: c = a :+: (b :+: c)                   ->
    (a :+: b) :+: succ c = a :+: (b :+: succ c)) as H4. {
      intros c H4 H5.
      assert (Ordinal (b :+: c)) as H6. { apply IsOrdinal; assumption. }
      rewrite WhenSuccR, WhenSuccR, WhenSuccR, H5; try assumption. reflexivity. }
  assert (forall c,
    Limit c                                                 ->
    (forall d, d :< c -> (a :+: b) :+: d = a :+: (b :+: d)) ->
    (a :+: b) :+: c = a :+: (b :+: c)) as H5. {
      intros c H5 H6.
      assert (Ordinal c) as H7. { apply H5. }
      assert (Limit (b :+: c)) as H8. { apply IsLimit; assumption. }
      assert ((a :+: b) :+: c :<=: a :+: (b :+: c)) as H9. {
        intros x H9.
        rewrite WhenLimit in H9. 2: assumption. apply SUG.Charac in H9.
        destruct H9 as [d [H9 H10]].
        assert (Ordinal d) as H11. { apply Core.IsOrdinal with c; assumption. }
        assert (x :< (a :+: b) :+: d) as H12. { assumption. }
        assert (x :< a :+: (b :+: d)) as H13. { rewrite <- H6; assumption. }
        rewrite WhenLimit. 2: assumption. apply SUG.Charac.
        exists (b :+: d). split. 2: assumption. apply ElemCompatR; assumption. }
      assert (a :+: (b :+: c) :<=: (a :+: b) :+: c) as H10. {
        intros x H10.
        rewrite WhenLimit in H10. 2: assumption. apply SUG.Charac in H10.
        destruct H10 as [e [H10 H11]].
        assert (Ordinal (b :+: c)) as H12. { apply H8. }
        assert (Ordinal e) as H13. {
          apply Core.IsOrdinal with (b :+: c); assumption. }
        assert (e :< b \/ b :<=: e) as H14. {
          apply Core.ElemOrIncl; assumption. }
        rewrite WhenLimit. 2: assumption. apply SUG.Charac.
        destruct H14 as [H14|H14].
        - exists :0:. split. 1: { apply Limit.HasZero. assumption. }
          assert (x :< (a :+: b) :+: :0:) as X. 2: apply X. (* failing rewrite *)
          rewrite WhenZeroR.
          assert (a :+: e :<=: a :+: b) as H15. {
            apply InclCompatR; try assumption.
            apply Core.ElemIsIncl; assumption. }
          apply H15. assumption.
        - assert (exists d, Ordinal d /\ b :+: d = e) as H15. {
            apply CompleteR; assumption. }
          destruct H15 as [d [H15 H16]].
          assert (d :< c) as H17. {
            assert (d :< c \/ c :<=: d) as H17. {
              apply Core.ElemOrIncl; assumption. }
            destruct H17 as [H17|H17]. 1: assumption.
            exfalso. apply (InclCompatR c d b) in H17; try assumption.
            rewrite H16 in H17.
            assert (e :< e) as H18. { apply H17. assumption. }
            revert H18. apply NoElemLoop1. }
          assert (x :< (a :+: b) :+: d) as H18. { rewrite H6, H16; assumption. }
          exists d. split; assumption. }
      apply DoubleInclusion. split; assumption. }
  apply Induction2.Induction; assumption.
Qed.

(* The addition of natural numbers is commutative.                              *)
Proposition Comm : forall (n m:U), n :< :N -> m :< :N ->
  n :+: m = m :+: n.
Proof.
  intros n m H1 H2. revert n H1.
  assert (Ordinal m) as H3. { apply Omega.HasOrdinalElem. assumption. }
  apply Omega.Induction.
  - rewrite WhenZeroL, WhenZeroR. 2: assumption. reflexivity.
  - intros n H4 IH.
    assert (Ordinal n) as H5. { apply Omega.HasOrdinalElem. assumption. }
    rewrite WhenSuccL, WhenSuccR, IH; try assumption. reflexivity.
Qed.

(* An non-integer ordinal is the sum of a limit ordinal and a natural number.   *)
Proposition Destruct : forall (a:U), Ordinal a ->
  :N :<=: a -> exists b n, Limit b /\ n :< :N /\ a = b :+: n.
Proof.
  intros a H1 H2.
  remember {{ x :< succ a | Limit }} as l eqn:H3.
  remember (sup l) as b eqn:H4.
  assert (Ordinal :N) as G1. { apply Omega.IsOrdinal. }
  assert (Limit :N) as G2. { apply Omega.IsLimit. }
  assert (toClass l :<=: Ordinal) as H5. {
    intros c H5. rewrite H3 in H5. apply Specify.IsInP in H5. apply H5. }
  assert (Ordinal b) as H6. { rewrite H4. apply Sup.IsOrdinal. }
  assert (b :<=: a) as H7. {
    rewrite H4. apply Sup.IsSmallest. 1: assumption.
    intros c H7. rewrite H3 in H7. apply Specify.IsInA in H7.
    apply Succ.InclIsElem; try assumption.
    apply Core.IsOrdinal with (succ a). 2: assumption.
    apply Succ.IsOrdinal. assumption. }
  assert (:N :< l) as H8. {
    rewrite H3. apply Specify.Charac. split. 2: assumption.
    apply Succ.InclIsElem; assumption. }
  assert (:N :<=: b) as H9. {
    rewrite H4. apply Sup.IsUpperBound; assumption. }
  assert (b <> :0:) as H10. {
    apply Empty.HasElem. exists :0:. apply H9, Omega.HasZero. }
  assert (Limit b) as H12. {
    apply Limit.WhenHasSucc; try assumption.
    intros d H12. rewrite H4 in H12. apply Sup.Charac in H12.
    destruct H12 as [c [H12 [H13 H14]]].
    assert (H15 := H13).
    rewrite H3 in H13. apply Specify.Charac in H13. destruct H13 as [H13 H16].
    assert (Ordinal d) as H17. { apply Core.IsOrdinal with c; assumption. }
    rewrite H4. apply Sup.Charac. exists c. split. 2: { split; assumption. }
    apply Limit.HasSucc; assumption. }
  assert (exists c, Ordinal c /\ b :+: c = a) as H13. {
    apply CompleteR; assumption. }
  destruct H13 as [c [H13 H14]].
  assert (c :< :N \/ :N :<=: c) as H15. {
    apply Core.ElemOrIncl; assumption. }
  destruct H15 as [H15|H15].
  - exists b. exists c. split. 1: assumption. split. 1: assumption.
    symmetry. assumption.
  - exfalso.
    assert (exists d, Ordinal d /\ :N :+: d = c) as H16. {
      apply CompleteR; assumption. }
    destruct H16 as [d [H16 H17]].
    assert (a = (b :+: :N) :+: d) as H18. {
      rewrite Assoc; try assumption. rewrite H17. symmetry. assumption. }
    assert (Limit (b :+: :N)) as H19. { apply IsLimit; assumption. }
    assert (b :+: :N :<=: a) as H20. {
      rewrite H18. apply IsInclR. 2: assumption. apply H19. }
    assert (b :+: :N :< l) as H21. {
      rewrite H3. apply Specify.Charac. split. 2: assumption.
      apply Succ.InclIsElem; try assumption. apply H19. }
    assert (b :< b :+: :N) as H22. {
      apply IsElemAddR; try assumption. apply Omega.IsNotEmpty. }
    revert H21 H22. rewrite H4. apply Sup.Contradict. 1: assumption.
    rewrite <- H4. apply H19.
Qed.

Proposition DestructUnique : forall (a b n m:U),
  Limit a             ->
  Limit b             ->
  n :< :N             ->
  m :< :N             ->
  a :+: n = b :+: m   ->
  a = b /\ n = m.
Proof.
  assert (forall (a b n m:U),
    Limit a             ->
    Limit b             ->
    a :<=: b            ->
    n :< :N             ->
    m :< :N             ->
    a :+: n = b :+: m   ->
    a = b /\ n = m) as H1. {
      intros a b n m H1 H2 H3 H4 H5 H6.
      assert (Ordinal a) as H7. { apply H1. }
      assert (Ordinal b) as H8. { apply H2. }
      assert (Ordinal :N) as H9. { apply Omega.IsOrdinal. }
      assert (Ordinal n) as H10. { apply HasOrdinalElem; assumption. }
      assert (Ordinal m) as H11. { apply HasOrdinalElem; assumption. }
      assert (exists c, Ordinal c /\ a :+: c = b) as H12. {
        apply CompleteR; assumption. }
      destruct H12 as [c [H12 H13]].
      assert (a :+: n = a :+: (c :+: m)) as H14. {
        rewrite <- Assoc; try assumption. rewrite H13. assumption. }
      assert (n = c :+: m) as H15. {
        apply CancelL with a; try assumption. apply IsOrdinal; assumption. }
      assert (c :<=: c :+: m) as H16. { apply IsInclR; assumption. }
      assert (c :< :N) as H17. {
        apply Core.InclElemTran with n; try assumption.
        rewrite H15. assumption. }
      assert (c = :0:) as H18. {
        revert H2. rewrite <- H13. apply LimitWithNat; assumption. }
      assert (n = m) as H19. {
        rewrite H18 in H15. rewrite WhenZeroL in H15; assumption. }
      assert (a = b) as H20. {
        rewrite H18 in H13. rewrite WhenZeroR in H13; assumption. }
      split; assumption. }
  intros a b n m H2 H3 H4 H5 H6.
  assert (Ordinal a) as H7. { apply H2. }
  assert (Ordinal b) as H8. { apply H3. }
  assert (a :<=: b \/ b :<=: a) as H9. { apply Core.InclOrIncl; assumption. }
  destruct H9 as [H9|H9].
  - apply H1; assumption.
  - assert (b = a /\ m = n) as H10. {
      apply H1; try assumption. symmetry. assumption. }
    destruct H10 as [H10 H11]. split; symmetry; assumption.
Qed.

Proposition LimitCharac : forall (a b:U), Ordinal a -> Ordinal b  ->
  Limit (a :+: b) <-> Limit b \/ (b = :0: /\ Limit a).
Proof.
  intros a b H1 H2.
  assert (Limit b \/ (b = :0: /\ Limit a) -> Limit (a :+: b)) as H3. {
    intros [H3|[H3 H4]].
    - apply IsLimit;assumption.
    - rewrite H3, WhenZeroR. assumption. }
  assert (Limit (a :+: b) -> Limit b \/ (b = :0: /\ Limit a)) as H4. {
    intros H4.
    assert (b :< :N \/ :N :<=: b) as H5. {
      apply Core.ElemOrIncl. 1: assumption. apply Omega.IsOrdinal. }
    destruct H5 as [H5|H5].
    - assert (a :< :N \/ :N :<=: a) as H6. {
      apply Core.ElemOrIncl. 1: assumption. apply Omega.IsOrdinal. }
      destruct H6 as [H6|H6].
      + exfalso. apply Limit.NotBoth with (a :+: b). 1: assumption.
        apply Omega.HasNonLimitElem, InOmega; assumption.
      + assert (exists c n, Limit c /\ n :< :N /\ a = c :+: n) as H7. {
          apply Destruct; assumption. }
        destruct H7 as [c [n [H7 [H8 H9]]]].
        assert (Ordinal c) as H10. { apply H7. }
        assert (Ordinal n) as H11. { apply Omega.HasOrdinalElem. assumption. }
        assert (n :+: b = :0:) as H12. {
          apply LimitWithNat with c. 1: assumption.
          - apply InOmega; assumption.
          - rewrite <- Assoc, <- H9; assumption. }
        apply WhenZero in H12; try assumption. destruct H12 as [H12 H13].
        rewrite H13, WhenZeroR in H4. right. split; assumption.
    - assert (exists c n, Limit c /\ n :< :N /\ b = c :+: n) as H6. {
        apply Destruct; assumption. }
      destruct H6 as [c [n [H6 [H7 H8]]]].
      assert (Ordinal c) as H9. { apply H6. }
      assert (Ordinal n) as H10. { apply Omega.HasOrdinalElem. assumption. }
      assert (n = :0:) as H11. {
        apply LimitWithNat with (a :+: c). 2: assumption.
        - apply IsLimit; assumption.
        - rewrite Assoc, <- H8; assumption. }
      rewrite H11 in H8. rewrite WhenZeroR in H8. rewrite <- H8 in H6.
      left. assumption. }
  split; assumption.
Qed.

Proposition HasAllSucc : forall (a b n:U),
  Limit a       ->
  b :< a        ->
  n :< :N       ->
  b :+: n :< a.
Proof.
  intros a b n H1 H2. revert n.
  apply Omega.Induction.
  - rewrite WhenZeroR. assumption.
  - intros n H3 IH.
    assert (Ordinal n) as H4. { apply Omega.HasOrdinalElem. assumption. }
    rewrite WhenSuccR. 2: assumption. apply Limit.HasSucc; assumption.
Qed.

