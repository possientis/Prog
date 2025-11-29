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
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
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

Proposition IsLimit : forall (a b:U), Ordinal a -> Ordinal b ->
  :0: :< a -> Limit b -> Limit (a :*: b).
Proof.
  intros a b H1 H2 H3 H4.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Ordinal :1:) as G2. { apply Natural.OneIsOrdinal. }
  assert (Ordinal (a :*: b)) as H5. { apply IsOrdinal; assumption. }
  assert (
    a :*: b = :0:              \/
    a :*: b = succ :U(a :*: b) \/
    Limit (a :*: b)) as H6. { apply Limit.ThreeWay. assumption. }
  destruct H6 as [H6|[H6|H6]]. 3: assumption.
  - exfalso. apply WhenZero in H6; try assumption. destruct H6 as [H6|H6].
    + rewrite H6 in H3. apply Empty.Charac in H3. contradiction.
    + rewrite H6 in H4. apply Limit.NotZero. assumption.
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
