Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Mult.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Sup.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Mult.
Export ZF.Notation.Mult.

Module COM := ZF.Class.Ordinal.Mult.
Module SOG := ZF.Set.Ordinal.UnionGenOfClass.
Module SUG := ZF.Set.UnionGenOfClass.


(* The product of two ordinals when a is an ordinal.                            *)
Definition mult (a b:U) : U := (COM.Mult a)!b.

(* Notation "a :*: b" := (mult a b)                                             *)
Global Instance SetMult : Mult U := { mult := mult }.

Proposition WhenZeroR : forall (a:U), a :*: :0: = :0:.
Proof.
  apply COM.WhenZero.
Qed.

Proposition WhenOneR : forall (a:U), Ordinal a ->
  a :*: :1: = a.
Proof.
  intros a H1.
  assert (a :*: :1: = a :*: :0: :+: a) as H2. {
    apply COM.WhenSucc, Core.ZeroIsOrdinal. }
  rewrite H2, WhenZeroR, Plus.WhenZeroL. 2: assumption.
  reflexivity.
Qed.

Proposition WhenSuccR : forall (a b:U), Ordinal b ->
  a :*: (succ b) = a :*: b :+: a.
Proof.
  apply COM.WhenSucc.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  a :*: b = :\/:_{b} (COM.Mult a).
Proof.
  apply COM.WhenLimit.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :*: a = :0:.
Proof.
  apply Induction2.
  - apply WhenZeroR.
  - intros a H1 H2. rewrite WhenSuccR. 2: assumption. rewrite H2.
    apply Plus.WhenZeroR.
  - intros a H1 H2. rewrite WhenLimit. 2: assumption.
    apply DoubleInclusion. split; intros x H3.
    + apply SUG.Charac in H3. destruct H3 as [y [H3 H4]].
      assert (x :< :0: :*: y) as H5. { apply H4. } (* rewrite H2 in H4 fails *)
      rewrite H2 in H5; assumption.
    + apply Empty.Charac in H3. contradiction.
Qed.

Proposition WhenOneL : forall (a:U), Ordinal a ->
  :1: :*: a = a.
Proof.
  apply Induction2.
  - apply WhenZeroR.
  - intros a H1 H2. rewrite WhenSuccR. 2: assumption. rewrite H2.
    apply Plus.WhenOneR.
  - intros a H1 H2. rewrite WhenLimit. 2: assumption.
    assert (Ordinal a) as G1. { apply H1. }
    apply DoubleInclusion. split; intros x H3.
    + apply SUG.Charac in H3. destruct H3 as [y [H3 H4]].
      assert (x :< :1: :*: y) as H5. { apply H4. } (* rewrite H2 in H4 fails *)
      rewrite H2 in H5. 2: assumption.
      assert (Ordinal y) as H6. { apply Core.IsOrdinal with a; assumption. }
      assert (Ordinal x) as H7. { apply Core.IsOrdinal with y; assumption. }
      apply Core.ElemElemTran with y; assumption.
    + apply SUG.Charac. exists (succ x).
      assert (succ x :< a) as G2. { apply Limit.HasSucc; assumption. }
      split. 1: assumption.
      assert (x :< :1: :*: succ x) as X. 2: apply X. (* rewrite H2 fails *)
      rewrite H2. 2: assumption. apply Succ.IsIn.
Qed.

Proposition IsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :*: b).
Proof.
  intros a b H1. revert b. apply Induction2.
  - rewrite WhenZeroR. apply Core.ZeroIsOrdinal.
  - intros b H2 H3. rewrite WhenSuccR. 2: assumption.
    apply Plus.IsOrdinal; assumption.
  - intros b H2 H3. rewrite WhenLimit. 2: assumption.
    apply SOG.IsOrdinal. apply H3.
Qed.

Proposition InOmega : forall (n m:U),
  n :< :N -> m :< :N -> n :*: m :< :N.
Proof.
  intros n m H1. revert m. apply Omega.FiniteInduction'.
  - rewrite WhenZeroR. apply Omega.HasZero.
  - intros m H2 H3.
    assert (Ordinal n) as H4. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal m) as H5. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal (n :*: m)) as H6. { apply IsOrdinal; assumption. }
    rewrite WhenSuccR. 2: assumption. apply Plus.InOmega; assumption.
Qed.

Proposition ElemCompatR : forall (a b c:U),
  Ordinal a           ->
  Ordinal b           ->
  Ordinal c           ->
  :0: :< c            ->
  a :< b              ->
  c :*: a :< c :*: b.
Proof.
  intros a b c H1 H2 H3 H4 H5. revert b H2 H5 c H3 H4.
  remember (fun b =>
    forall c : U, Ordinal c -> :0: :< c -> c :*: a :< c :*: b) as A eqn:H6.
  assert (Ordinal (succ a)) as H7. { apply Succ.IsOrdinal. assumption. }
  assert (forall b, Ordinal b -> succ a :<=: b -> A b) as H8. {
    apply Induction2'. 1: assumption.
    - rewrite H6. intros c H8 H9. rewrite WhenSuccR. 2: assumption.
      apply Plus.IsElemAddR. 2: assumption.
      + apply IsOrdinal; assumption.
      + apply Empty.HasElem. exists :0:. assumption.
    - rewrite H6. intros b H8 H9 IH c H10 H11. rewrite WhenSuccR. 2: assumption.
      assert (Ordinal (c :*: b)) as H12. { apply IsOrdinal; assumption. }
      apply ElemElemTran with (c :*: b). 2: assumption.
      + apply IsOrdinal; assumption.
      + apply Plus.IsOrdinal; assumption.
      + apply IH; assumption.
      + apply Plus.IsElemAddR; try assumption.
        apply Empty.HasElem. exists :0:. assumption.
    - rewrite H6. intros b H8 H9 IH c H10 H11.
      rewrite (WhenLimit c b). 2: assumption. apply SUG.Charac.
      assert (succ a :< b) as H12. {
        apply Limit.HasSucc. 1: assumption. apply H9, Succ.IsIn. }
      exists (succ a). split. 1: assumption.
      apply IH; try assumption.
      + apply Incl.Refl. }
  rewrite H6 in H8. intros b H9 H10. apply H8. 1: assumption.
  apply ElemIsIncl; assumption.
Qed.

Proposition InclCompatRevR : forall (a b c:U),
  Ordinal a             ->
  Ordinal b             ->
  Ordinal c             ->
  :0: :< c              ->
  c :*: a :<=: c :*: b  ->
  a :<=: b.
Proof.
  intros a b c H1 H2 H3 H4 H5.
  assert (b :< a \/ a :<=: b) as H6. { apply Core.ElemOrIncl; assumption. }
  destruct H6 as [H6|H6]. 2: assumption. exfalso.
  assert (c :*: b :< c :*: a) as H7. { apply ElemCompatR; assumption. }
  assert (c :*: b :< c :*: b) as H8. { apply H5. assumption. }
  revert H8. apply NoElemLoop1.
Qed.

Proposition IsNotZeroL : forall (a b c:U),
  Ordinal a           ->
  Ordinal b           ->
  Ordinal c           ->
  c :*: a :< c :*: b  ->
  :0: :< c.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (c = :0: \/ :0: :< c) as H5. { apply Core.ZeroOrElem. assumption. }
  destruct H5 as [H5|H5]. 2: assumption.
  exfalso. subst. rewrite WhenZeroL, WhenZeroL in H4; try assumption.
  apply Empty.Charac in H4. contradiction.
Qed.

Proposition IsNotZeroR : forall (a b c:U),
  Ordinal a           ->
  Ordinal b           ->
  Ordinal c           ->
  a :*: c :< b :*: c  ->
  :0: :< c.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (c = :0: \/ :0: :< c) as H5. { apply Core.ZeroOrElem. assumption. }
  destruct H5 as [H5|H5]. 2: assumption.
  exfalso. subst. rewrite WhenZeroR, WhenZeroR in H4; try assumption.
  apply Empty.Charac in H4. contradiction.
Qed.

Proposition ElemCompatRevR : forall (a b c:U),
  Ordinal a           ->
  Ordinal b           ->
  Ordinal c           ->
  c :*: a :< c :*: b  ->
  a :< b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (Ordinal (c :*: b)) as G1. { apply IsOrdinal; assumption. }
  assert (:0: :< c) as H5. { apply IsNotZeroL with a b; assumption. }
  assert (a :<=: b) as H6. {
    apply InclCompatRevR with c; try assumption.
    apply Core.ElemIsIncl; assumption. }
  assert (a = b \/ a :< b) as H7. { apply Core.InclIsEqualOrElem; assumption. }
  destruct H7 as [H7|H7]. 2: assumption. subst. exfalso.
  revert H4. apply NoElemLoop1.
Qed.

Proposition InclCompatR : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  a :<=: b                ->
  c :*: a :<=: c :*: b.
Proof.
  intros a b c H1 H2 H3 H4.
  assert (c = :0: \/ :0: :< c) as H5. { apply Core.ZeroOrElem. assumption. }
  destruct H5 as [H5|H5].
  - subst. rewrite WhenZeroL, WhenZeroL; try assumption. apply Incl.Refl.
  - assert (a = b \/ a :< b) as H6. { apply Core.InclIsEqualOrElem; assumption. }
    destruct H6 as [H6|H6].
    + subst. apply Incl.Refl.
    + apply Core.ElemIsIncl.
      * apply IsOrdinal; assumption.
      * apply ElemCompatR; assumption.
Qed.

Proposition CancelL : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  :0: :< c                ->
  c :*: a = c :*: b       ->
  a = b.
Proof.
  intros a b c H1 H2 H3 H4 H5.
  assert (a = b \/ a :< b \/ b :< a) as H6. { apply Core.IsTotal; assumption. }
  destruct H6 as [H6|[H6|H6]]. 1: assumption.
  - assert (c :*: a :< c :*: b) as H7. { apply ElemCompatR; assumption. }
    exfalso. rewrite H5 in H7. revert H7. apply NoElemLoop1.
  - assert (c :*: b :< c :*: a) as H7. { apply ElemCompatR; assumption. }
    exfalso. rewrite H5 in H7. revert H7. apply NoElemLoop1.
Qed.

Proposition InclCompatL : forall (a b c:U),
  Ordinal a               ->
  Ordinal b               ->
  Ordinal c               ->
  a :<=: b                ->
  a :*: c :<=: b :*: c.
Proof.
  intros a b c H1 H2 H3 H4. revert c H3.
  apply Induction2.
  - rewrite WhenZeroR, WhenZeroR. apply Incl.Refl.
  - intros c H3 IH.
    rewrite WhenSuccR, WhenSuccR; try assumption.
    apply Plus.InclCompat; try assumption; apply IsOrdinal; assumption.
  - intros c H3 IH.
    rewrite WhenLimit, WhenLimit; try assumption. intros y H5.
    apply SUG.Charac in H5. destruct H5 as [x [H5 H6]].
    apply SUG.Charac. exists x. split. 1: assumption.
    apply IH; assumption.
Qed.

Proposition WhenZero : forall (a b:U), Ordinal a -> Ordinal b ->
  a :*: b = :0: <-> a = :0: \/ b = :0:.
Proof.
  intros a b H1 H2. split; intros H3.
  - assert (a = :0: \/ :0: :< a) as H4. { apply Core.ZeroOrElem. assumption. }
    assert (b = :0: \/ :0: :< b) as H5. { apply Core.ZeroOrElem. assumption. }
    assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
    destruct H4 as [H4|H4]; destruct H5 as [H5|H5].
    + left.  assumption.
    + left.  assumption.
    + right. assumption.
    + assert (:1: :<=: a) as H6. { apply Succ.ElemIsIncl; assumption. }
      assert (:1: :<=: b) as H7. { apply Succ.ElemIsIncl; assumption. }
      assert (a :*: :1: :<=: a :*: b) as H8. {
        apply InclCompatR; try assumption. apply Natural.OneIsOrdinal. }
      rewrite WhenOneR in H8; try assumption. rewrite H3 in H8.
      assert (:0: :< :0:) as H9. { apply H8. assumption. }
      apply Empty.Charac in H9. contradiction.
  - destruct H3 as [H3|H3]; rewrite H3.
    + rewrite WhenZeroL. 2: assumption. reflexivity.
    + rewrite WhenZeroR. reflexivity.
Qed.

Proposition IsLimit : forall (a b:U), Ordinal a ->
  :0: :< a -> Limit b -> Limit (a :*: b).
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (Ordinal b) as G3. { apply H3. }
  assert (Ordinal (a :*: b)) as H5. { apply IsOrdinal; assumption. }
  assert (
    a :*: b = :0:              \/
    a :*: b = succ :U(a :*: b) \/
    Limit (a :*: b)) as H6. { apply Limit.ThreeWay. assumption. }
  destruct H6 as [H6|[H6|H6]]. 3: assumption.
  - exfalso. apply WhenZero in H6; try assumption. destruct H6 as [H6|H6].
    + rewrite H6 in H2. apply Empty.Charac in H2. contradiction.
    + rewrite H6 in H3. apply Limit.NotZero. assumption.
  - exfalso. remember (:U(a :*: b)) as c eqn:H7.
    assert (c :< a :*: b) as H8. { rewrite H6. apply Succ.IsIn. }
    rewrite WhenLimit in H8. 2: assumption.
    apply SUG.Charac in H8. destruct H8 as [d [H8 H9]].
    assert (c :< a :*: d) as H10. { assumption. }
    assert (Ordinal d) as H11. { apply Core.IsOrdinal with b; assumption. }
    assert (Ordinal (a :*: d)) as H12. { apply IsOrdinal; assumption. }
    assert (Ordinal c) as H13. {
      apply Core.IsOrdinal with (a :*: d); assumption. }
    assert (succ c :< a :*: d :+: :1:) as H14. {
      rewrite Plus.WhenOneR. apply Succ.ElemCompat; assumption. }
    assert (:1: :<=: a) as H15. { apply Succ.ElemIsIncl; assumption. }
    assert (succ c :< a :*: succ d) as H16. {
      apply Core.ElemInclTran with (a :*: d :+: :1:); try assumption.
      - apply Succ.IsOrdinal. assumption.
      - apply Plus.IsOrdinal; assumption.
      - apply IsOrdinal. 1: assumption. apply Succ.IsOrdinal. assumption.
      - rewrite WhenSuccR. 2: assumption. apply Plus.InclCompatR; assumption. }
    assert (succ c :< a :*: b) as H17. {
      rewrite WhenLimit. 2: assumption.
      apply SUG.Charac. exists (succ d). split. 2: assumption.
      apply Limit.HasSucc; assumption. }
    rewrite H6 in H17. revert H17. apply NoElemLoop1.
Qed.

(* Note that (N+1)*2 = (N+1)+(N+1) = N*2+1 <> N*2+2 so there is no DistribR.    *)
Proposition DistribL : forall (a b c:U), Ordinal a -> Ordinal b -> Ordinal c ->
  a :*: (b :+: c) = a :*: b :+: a :*: c.
Proof.
  intros a b c H1 H2. revert c.
  apply Induction2.
  - rewrite Plus.WhenZeroR, WhenZeroR, Plus.WhenZeroR. reflexivity.
  - intros c H3 IH.
    assert (Ordinal (b :+: c)) as H4. { apply Plus.IsOrdinal; assumption. }
    rewrite Plus.WhenSuccR, (WhenSuccR a (b :+: c)); try assumption.
    rewrite IH, WhenSuccR; try assumption.
    rewrite <- Plus.Assoc. 1: reflexivity. 3: assumption.
    + apply IsOrdinal; assumption.
    + apply IsOrdinal; assumption.
  - intros c H3 IH.
    assert (Ordinal c) as H4. { apply H3. }
    assert (Ordinal (b :+: c)) as H5. { apply Plus.IsOrdinal; assumption. }
    assert (Limit (b :+: c)) as H6. { apply Plus.IsLimit; assumption. }
    assert (Ordinal (a :*: b)) as G4. { apply IsOrdinal; assumption. }
    assert (a = :0: \/ :0: :< a) as H7. { apply Core.ZeroOrElem. assumption. }
    destruct H7 as [H7|H7].
    + subst. rewrite WhenZeroL, WhenZeroL, WhenZeroL, Plus.WhenZeroR;
      try assumption. reflexivity.
    + assert (Limit (a :*: c)) as H8. { apply IsLimit; assumption. }
      assert (Ordinal (a :*: c)) as G1. { apply H8. }
      rewrite (WhenLimit a (b :+: c)). 2: assumption.
      rewrite (Plus.WhenLimit (a :*: b) (a :*: c)). 2: assumption.
      apply DoubleInclusion. split; intros y H9;
      apply SUG.Charac in H9; apply SUG.Charac.
      * destruct H9 as [d [H9 H10]].
        assert (Ordinal d) as H11. {
          apply Core.IsOrdinal with (b :+: c); assumption. }
        assert (d :< b \/ b :<=: d) as H12. { apply Core.ElemOrIncl; assumption. }
        assert (Ordinal (a :*: d)) as G2. { apply IsOrdinal; assumption. }
        assert (Ordinal y) as G3. {
          apply Core.IsOrdinal with (a :*: d); assumption. }
        destruct H12 as [H12|H12].
          { exists :0:. split.
            - assert (a :*: c = :0: \/ :0: :< a :*: c) as H13. {
                apply Core.ZeroOrElem. assumption. }
              destruct H13 as [H13|H13]. 2: assumption.
              apply WhenZero in H13; try assumption. destruct H13 as [H13|H13].
              + rewrite H13 in H7. apply Empty.Charac in H7. contradiction.
              + exfalso. rewrite H13 in H3. apply Limit.NotZero. assumption.
            - assert (y :< a :*: b :+: :0:) as X. 2: apply X.
              rewrite Plus.WhenZeroR.
              apply Core.ElemElemTran with (a :*: d); try assumption.
              apply ElemCompatR; assumption. }
          { assert (exists e, Ordinal e /\ b :+: e = d) as H13. {
              apply Plus.CompleteR; assumption. }
            destruct H13 as [e [H13 H14]].
            assert (e :< c) as H15. {
              apply Plus.ElemCompatRevR with b; try assumption.
              rewrite H14. assumption. }
            exists (a :*: e). split.
            - apply ElemCompatR; assumption.
            - assert (y :< a :*: b :+: a :*: e) as X. 2: apply X.
              rewrite <- IH, H14; assumption. }
      * destruct H9 as [e [H9 H10]].
        rewrite WhenLimit in H9. 2: assumption.
        apply SUG.Charac in H9. destruct H9 as [d [H9 H11]].
        assert (Ordinal d) as H12. { apply Core.IsOrdinal with c; assumption. }
        assert (Ordinal (a :*: d)) as G5. { apply IsOrdinal; assumption. }
        assert (Ordinal e) as G6. {
          apply Core.IsOrdinal with (a :*: d); assumption. }
        assert (b :+: d :< b :+: c) as H13. {
          apply Plus.ElemCompatR; assumption. }
        assert (a :*: b :+: e :< a :*: (b :+: d)) as H14. {
          rewrite IH. 2: assumption. apply Plus.ElemCompatR; assumption. }
        exists (b :+: d). split. 1: assumption.
        apply Core.ElemIsIncl in H14.
          { apply H14. assumption. }
          { apply IsOrdinal. 1: assumption. apply Plus.IsOrdinal; assumption. }
Qed.

Proposition Assoc : forall (a b c:U), Ordinal a -> Ordinal b -> Ordinal c ->
  (a :*: b) :*: c = a :*: (b :*: c).
Proof.
  intros a b c H1 H2. revert c.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  apply Induction2.
  - rewrite WhenZeroR, WhenZeroR, WhenZeroR. reflexivity.
  - intros c H3 IH.
    rewrite WhenSuccR, IH, <- DistribL, <- WhenSuccR; try assumption.
    + reflexivity.
    + apply IsOrdinal; assumption.
  - intros c H3 IH.
    assert (Ordinal c) as G2. { apply H3. }
    assert (Ordinal (b :*: c)) as G3. { apply IsOrdinal; assumption. }
    assert (a = :0: \/ :0: :< a) as H4. { apply Core.ZeroOrElem. assumption. }
    assert (b = :0: \/ :0: :< b) as H5. { apply Core.ZeroOrElem. assumption. }
    destruct H4 as [H4|H4]; destruct H5 as [H5|H5].
    + subst. rewrite WhenZeroR, WhenZeroL, WhenZeroR; try assumption.
      reflexivity.
    + subst. rewrite WhenZeroL, WhenZeroL, WhenZeroL; try assumption.
      reflexivity.
    + subst. rewrite WhenZeroR, WhenZeroL, WhenZeroR; try assumption.
      reflexivity.
    + assert (Limit (b :*: c)) as H6. { apply IsLimit; assumption. }
      rewrite (WhenLimit (a :*: b) c). 2: assumption.
      rewrite (WhenLimit a (b :*: c)). 2: assumption.
      apply DoubleInclusion. split; intros y H7;
      apply SUG.Charac in H7; apply SUG.Charac.
      * destruct H7 as [d [H7 H8]]. exists (b :*: d).
        assert (Ordinal d) as H9. { apply Core.IsOrdinal with c; assumption. }
        split.
          { apply ElemCompatR; assumption. }
          { assert (y :< a :*: (b :*: d)) as X. 2: apply X.
            rewrite <- IH; assumption. }
      * destruct H7 as [e [H7 H8]].
        rewrite WhenLimit in H7. 2: assumption.
        apply SUG.Charac in H7. destruct H7 as [d [H7 H9]].
        assert (Ordinal d) as H10. { apply Core.IsOrdinal with c; assumption. }
        assert (Ordinal (b :*: d)) as H11. { apply IsOrdinal; assumption. }
        assert (Ordinal e) as H12. {
          apply Core.IsOrdinal with (b :*: d); assumption. }
        exists d. split. 1: assumption.
        assert (y :< (a :*: b) :*: d) as X. 2: apply X.
        rewrite IH. 2: assumption.
        assert (e :<=: b :*: d) as H13. { apply Core.ElemIsIncl; assumption. }
        assert (a :*: e :<=: a :*: (b :*: d)) as H14. {
          apply InclCompatR; assumption. }
        apply H14. assumption.
Qed.

Proposition IsInclMultL : forall (a b:U), Ordinal a -> Ordinal b  ->
  :0: :< b -> a :<=: b :*: a.
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal :0:) as H4. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as H5. { apply Natural.OneIsOrdinal. }
  assert (:1: :<=: b) as H6. { apply Succ.ElemIsIncl; assumption. }
  assert (:1: :*: a :<=: b :*: a) as H7. { apply InclCompatL; assumption. }
  rewrite WhenOneL in H7; assumption.
Qed.

Proposition IsInclMultR : forall (a b:U), Ordinal a -> Ordinal b  ->
  :0: :< b -> a :<=: a :*: b.
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal :0:) as H4. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as H5. { apply Natural.OneIsOrdinal. }
  assert (:1: :<=: b) as H6. { apply Succ.ElemIsIncl; assumption. }
  assert (a :*: :1: :<=: a :*: b) as H7. { apply InclCompatR; assumption. }
  rewrite WhenOneR in H7; assumption.
Qed.

Proposition Euclid : forall (a b:U),
  Ordinal a             ->
  Ordinal b             ->
  :0: :< b              ->
  exists c d,
    Ordinal c           /\
    Ordinal d           /\
    a = b :*: c :+: d   /\
    d :< b.
Proof.
  intros a b H1 H2 H3.
  assert (a :< b \/ b :<=: a) as H4. { apply Core.ElemOrIncl; assumption. }
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (Ordinal (succ a)) as G3. { apply Succ.IsOrdinal. assumption. }
  destruct H4 as [H4|H4].
  - exists :0:. exists a. split. 1: assumption. split. 1: assumption.
    split. 2: assumption. rewrite WhenZeroR, Plus.WhenZeroL. 2: assumption.
    reflexivity.
  - remember {{x :< succ a | fun d => b :*: d :<=: a}} as A eqn:H5.
    remember (sup A) as c eqn:H6.
    assert (toClass A :<=: Ordinal) as G4. {
      intros d G4.
      rewrite H5 in G4. apply Specify.Charac in G4. destruct G4 as [G4 G5].
      apply Core.IsOrdinal with (succ a); assumption. }
    assert (Ordinal c) as H7. { rewrite H6. apply Sup.IsOrdinal. }
    assert (Ordinal (succ c)) as G5. { apply Succ.IsOrdinal. assumption. }
    assert (:1: :<=: b) as H8. { apply Succ.ElemIsIncl; assumption. }
    assert (:1: :< A) as H9. {
      rewrite H5. apply Specify.Charac. split.
      - apply Succ.InclIsElem; try assumption.
        apply Incl.Tran with b; assumption.
      - rewrite WhenOneR; assumption. }
    assert (:1: :<=: c) as H10. {
      rewrite H6. apply Sup.IsUpperBound; assumption. }
    assert (forall d, Ordinal d -> b :*: d :<=: a -> d :< succ a) as G6. {
      intros d G6 G7.
      assert (d :< succ a \/ succ a :<=: d) as G8. {
        apply Core.ElemOrIncl; assumption. }
      destruct G8 as [G8|G8]. 1: assumption. exfalso.
      apply Succ.ElemIsIncl in G8; try assumption.
      assert (b :*: a :< a) as G9. {
        apply Core.ElemInclTran with (b :*: d); try assumption.
        - apply IsOrdinal; assumption.
        - apply IsOrdinal; assumption.
        - apply ElemCompatR; assumption. }
      assert (:1: :*: a :<=: b :*: a) as G10. { apply InclCompatL; assumption. }
      rewrite WhenOneL in G10. 2: assumption.
      assert (b :*: a :< b :*: a) as G11. { apply G10. assumption. }
      revert G11. apply NoElemLoop1. }
    assert (forall d, Ordinal d -> d :< c -> b :*: d :<=: a) as H11. {
      intros d H11 H12.
      assert (Ordinal (b :*: d)) as H13. { apply IsOrdinal; assumption. }
      assert (a :< b :*: d \/ b :*: d :<=: a) as H14. {
        apply Core.ElemOrIncl; assumption. }
      destruct H14 as [H14|H14]. 2: assumption. exfalso.
      assert (c :<=: d) as H15. {
        rewrite H6. apply Sup.IsSmallest. 1: assumption.
        intros e H15. rewrite H5 in H15.
        apply Specify.Charac in H15. destruct H15 as [H15 H16].
        apply InclCompatRevR with b; try assumption.
        - apply Core.IsOrdinal with (succ a); assumption.
        - apply Incl.Tran with a. 1: assumption.
          apply Core.ElemIsIncl; assumption. }
      assert (d :< d) as H17. { apply H15. assumption. }
      revert H17. apply NoElemLoop1. }
    assert (b :*: c :<=: a) as H12. {
      assert (c = :0: \/ c = succ :U(c) \/ Limit c) as H12. {
        apply Limit.ThreeWay. assumption. }
      destruct H12 as [H12|[H12|H12]].
      - exfalso. rewrite H12 in H10. apply OneNotLessThanZero. assumption.
      - remember :U(c) as e eqn:H13.
        assert (Ordinal e) as H14. {
          apply Succ.IsOrdinalRev. rewrite <- H12. assumption. }
        assert (e :< c) as H15. { rewrite H12. apply Succ.IsIn. }
        assert (exists f, Ordinal f /\ f :< A /\ e :< f) as H16. {
          rewrite H6 in H15. apply Sup.WhenLess; assumption. }
        destruct H16 as [f [H16 [H17 H18]]].
        assert (f = c) as H19. {
          rewrite H12. apply Succ.InBetween; try assumption.
          rewrite <- H12, H6. apply Sup.IsUpperBound; assumption. }
        rewrite H19 in H17. rewrite H5 in H17. apply Specify.Charac in H17.
        apply H17.
      - rewrite WhenLimit. 2: assumption. intros y H13.
        apply SUG.Charac in H13. destruct H13 as [d [H13 H14]].
        assert (Ordinal d) as H16. { apply Core.IsOrdinal with c; assumption. }
        apply H11 with d; assumption. }
    assert (Ordinal (b :*: c)) as H13. { apply IsOrdinal; assumption. }
    assert (exists d, Ordinal d /\ b :*: c :+: d = a) as H14. {
      apply Plus.CompleteR; assumption. }
    destruct H14 as [d [H14 H15]]. exists c. exists d. split. 1: assumption.
    split. 1: assumption. split. 1: { symmetry. assumption. }
    assert (d :< b \/ b :<=: d) as H16. { apply Core.ElemOrIncl; assumption. }
    destruct H16 as [H16|H16]. 1: assumption. exfalso.
    assert (exists e, Ordinal e /\ b :+: e = d) as H17. {
      apply Plus.CompleteR; assumption. }
    destruct H17 as [e [H17 H18]].
    assert (a = b :*: (succ c) :+: e) as H19. {
      rewrite WhenSuccR, Plus.Assoc; try assumption.
      rewrite H18. symmetry. assumption. }
    assert (Ordinal (b :*: succ c)) as H20. { apply IsOrdinal; assumption. }
    assert (b :*: succ c :<=: a) as H21. {
      rewrite H19. apply IsInclPlusR; assumption. }
    assert (succ c :< A) as H22. {
      rewrite H5. apply Specify.Charac. split. 2: assumption.
      apply G6; assumption. }
    assert (succ c :<=: sup A) as H23. { apply Sup.IsUpperBound; assumption. }
    rewrite <- H6 in H23.
    assert (c :< c) as H24. { apply H23, Succ.IsIn. }
    revert H24. apply NoElemLoop1.
Qed.

Proposition EuclidUnique : forall (b c1 c2 d1 d2:U),
  Ordinal b                           ->
  Ordinal c1                          ->
  Ordinal c2                          ->
  Ordinal d1                          ->
  Ordinal d2                          ->
  d1 :< b                             ->
  d2 :< b                             ->
  b :*: c1 :+: d1 = b :*: c2 :+: d2   ->
  c1 = c2 /\ d1 = d2.
Proof.
  assert (forall b c1 c2 d1 d2,
    Ordinal b                           ->
    Ordinal c1                          ->
    Ordinal c2                          ->
    Ordinal d1                          ->
    Ordinal d2                          ->
    d1 :< b                             ->
    d2 :< b                             ->
    b :*: c1 :+: d1 = b :*: c2 :+: d2   ->
    c1 :<=: c2                          ->
    c1 = c2 /\ d1 = d2) as G1. {
      intros b c1 c2 d1 d2 H1 H2 H3 H4 H5 H6 H7 H8 H9.
      assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
      assert (exists e, Ordinal e /\ c1 :+: e = c2) as H10. {
        apply Plus.CompleteR; assumption. }
      destruct H10 as [e [H10 H11]].
      assert (b :*: c1 :+: d1 = b :*: c1 :+: b :*: e :+: d2) as H12. {
        rewrite <- DistribL, H11; assumption. }
      assert (Ordinal (b :*: e)) as H13. { apply IsOrdinal; assumption. }
      assert (Ordinal (b :*: e :+: d2)) as H14. {
        apply Plus.IsOrdinal; assumption. }
      assert (Ordinal (b :*: c1)) as H15. { apply IsOrdinal; assumption. }
      assert (d1 = b :*: e :+: d2) as H16. {
        apply Plus.CancelL with (b :*: c1); try assumption.
        rewrite <- Plus.Assoc; assumption. }
      assert (e = :0: \/ :0: :< e) as H17. { apply Core.ZeroOrElem. assumption. }
      destruct H17 as [H17|H17].
      - subst. rewrite Plus.WhenZeroR, WhenZeroR, Plus.WhenZeroL. 2: assumption.
        split; reflexivity.
      - exfalso.
        assert (b :<=: d1) as H18. {
          rewrite H16.
          apply Incl.Tran with (b :*: e).
          - apply IsInclMultR; assumption.
          - apply IsInclPlusR; assumption. }
        assert (d1 :< d1) as H19. { apply H18. assumption. }
        revert H19. apply NoElemLoop1. }
  intros b c1 c2 d1 d2 H1 H2 H3 H4 H5 H6 H7 H8.
  assert (c1 :<=: c2 \/ c2 :<=: c1) as H9. { apply Core.InclOrIncl; assumption. }
  destruct H9 as [H9|H9].
  - apply G1 with b; assumption.
  - assert (c2 = c1 /\ d2 = d1) as H10. {
      apply G1 with b; try assumption. symmetry. assumption. }
    split; symmetry; apply H10.
Qed.

