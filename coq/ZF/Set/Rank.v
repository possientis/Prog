Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.R1.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.
Require Import ZF.Set.WellFounded.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module CIN := ZF.Class.Incl.
Module COI := ZF.Class.Ordinal.Induction.
Module SUG := ZF.Set.UnionGenOfClass.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* Given a set a, the class underlying the rank of a.                           *)
Definition K (a:U) : Class := fun b => Ordinal b /\ a :< R1!(succ b).

(* The rank of a set a.                                                         *)
Definition rank (a:U) : U := inf (K a).

Lemma IsIncl : forall (a:U), K a :<=: Ordinal.
Proof.
  intros a b H1. apply H1.
Qed.

Lemma IsNotEmpty : forall (a:U), K a :<>: :0:.
Proof.
  intros a.
  remember (fun b => Ordinal b /\ a :< R1!b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. {
    rewrite H1. apply CEM.HasElem. apply IsWellFounded. }
  assert (exists b, Ordinal b /\ A b /\ forall c, A c -> b :<=: c) as H4. {
    apply Core.HasMinimal; assumption. }
  destruct H4 as [b [H4 [H5 H6]]].
  assert (a :< R1!b) as H7. { rewrite H1 in H5. apply H5. }
  assert (Successor b) as H8. {
    assert (b = :0: \/ Successor b \/ Limit b) as H8. {
      apply Limit.ThreeWay. assumption. }
    destruct H8 as [H8|[H8|H8]]. 2: assumption.
    - exfalso. rewrite H8 in H7. rewrite R1.WhenZero in H7.
      apply Empty.Charac in H7. contradiction.
    - exfalso. rewrite R1.WhenLimit in H7. 2: assumption.
      apply SUG.Charac in H7. destruct H7 as [c [H7 H9]].
      assert (Ordinal c) as H10. { apply Core.IsOrdinal with b; assumption. }
      assert (A c) as H11. { rewrite H1. split; assumption. }
      assert (c :< c) as H12. { apply H6; assumption. }
      revert H12. apply NoElemLoop1. }
  destruct H8 as [_ [c H8]].
  assert (Ordinal c) as H9. {
    apply Succ.IsOrdinalRev. rewrite <- H8. assumption. }
  apply CEM.HasElem. exists c. split. 1: assumption.
  rewrite <- H8. assumption.
Qed.

Proposition IsOrdinal : forall (a:U), Ordinal (rank a).
Proof.
  intros a. apply SOI.IsOrdinal.
Qed.

Proposition IsIn : forall (a b:U), Ordinal b ->
  rank a :< b -> a :< R1!b.
Proof.
  intros a b H1 H2.
  assert (K a (rank a)) as H3. {
    apply (SOI.IsIn (K a)).
    - apply IsIncl.
    - apply IsNotEmpty. }
  destruct H3 as [H3 H4].
  apply R1.InclCompat with (succ (rank a)); try assumption.
  - apply Succ.IsOrdinal. assumption.
  - apply Succ.ElemIsIncl; assumption.
Qed.

Proposition IsNotIn : forall (a b:U), Ordinal b ->
  b :<=: rank a -> ~ a :< R1!b.
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal (rank a)) as G1. { apply IsOrdinal. }
  assert (Ordinal (succ (rank a))) as G2. { apply Succ.IsOrdinal. assumption. }
  remember (fun c => Ordinal c /\ a :< R1!c) as A eqn:H4.
  assert (A :<=: Ordinal) as H5. { rewrite H4. intros c H5. apply H5. }
  assert (A :<>: :0:) as H6. {
    rewrite H4. apply CEM.HasElem. apply IsWellFounded. }
  assert (exists c, Ordinal c /\ A c /\ forall d, A d -> c :<=: d) as H7. {
    apply Core.HasMinimal; assumption. }
  destruct H7 as [c [H7 [H8 H9]]].
  assert (a :< R1!c) as H10. { rewrite H4 in H8. apply H8. }
  assert (Successor c) as H11. {
    assert (c = :0: \/ Successor c \/ Limit c) as H11. {
      apply Limit.ThreeWay. assumption. }
    destruct H11 as [H11|[H11|H11]]. 2: assumption.
    - exfalso. rewrite H11 in H10. rewrite R1.WhenZero in H10.
      apply Empty.Charac in H10. contradiction.
    - exfalso. rewrite R1.WhenLimit in H10. 2: assumption.
      apply SUG.Charac in H10. destruct H10 as [d [H10 H12]].
      assert (Ordinal d) as H13. { apply Core.IsOrdinal with c; assumption. }
      assert (A d) as H14. { rewrite H4. split; assumption. }
      assert (d :< d) as H15. { apply H9; assumption. }
      revert H15. apply NoElemLoop1. }
  destruct H11 as [_ [d H11]].
  assert (Ordinal d) as H12. {
    apply Succ.IsOrdinalRev. rewrite <- H11. assumption. }
  assert (c :<=: succ (rank a)) as H13. {
    apply H9. rewrite H4. split. 1: assumption. apply IsIn. 1: assumption.
    apply Succ.IsIn. }
  assert (succ (rank a) :<=: c) as H14. {
    rewrite H11. apply Succ.InclCompat; try assumption.
    apply SOI.IsLowerBound.
    - apply IsIncl.
    - split. 1: assumption. rewrite <- H11. assumption. }
  assert (c = succ (rank a)) as H15. {
    apply Incl.DoubleInclusion. split; assumption. }
  assert (c :<=: b) as H16. { apply H9. rewrite H4. split; assumption. }
  assert (rank a :< rank a) as H17. {
    apply H2, H16. rewrite H15. apply Succ.IsIn. }
  revert H17. apply NoElemLoop1.
Qed.

Proposition IsLowerBound : forall (a b:U), Ordinal b ->
  a :< R1!b -> rank a :< b.
Proof.
  intros a b H1 H2.
  assert (Ordinal (rank a)) as G1. { apply IsOrdinal. }
  assert (Ordinal (succ (rank a))) as G2. { apply Succ.IsOrdinal. assumption. }
  assert (rank a :< b \/ b :<=: rank a) as H3. {
    apply Core.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3]. 1: assumption.
  assert (~ a :< R1!b) as H6. { apply IsNotIn; assumption. }
  contradiction.
Qed.

Proposition IsLargest : forall (a b:U), Ordinal b ->
  ~ a :< R1!b -> b :<=: rank a.
Proof.
  intros a b H1 H2.
  assert (Ordinal (rank a)) as G1. { apply IsOrdinal. }
  assert (rank a :< b \/ b :<=: rank a) as H3. {
    apply Core.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3]. 2: assumption. exfalso.
  assert (a :< R1!b) as H4. { apply IsIn; assumption. }
  contradiction.
Qed.

Proposition  Equal : forall (a b:U), Ordinal b ->
  b = rank a <-> ~ a :< R1!b /\ a :< R1!(succ b).
Proof.
  intros a b H1.
  assert (Ordinal (succ b)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal (rank a)) as G2. { apply IsOrdinal. }
  split; intros H2.
  - split.
    + apply IsNotIn. 1: assumption. subst. apply Incl.Refl.
    + apply IsIn. 1: assumption. subst. apply Succ.IsIn.
  - destruct H2 as [H2 H3]. apply Incl.DoubleInclusion. split.
    + apply IsLargest; assumption.
    + apply Succ.InclCompatRev; try assumption.
      apply Succ.ElemIsIncl; try assumption.
      apply IsLowerBound; assumption.
Qed.

Proposition ElemCompat : forall (a b:U),
  a :< b -> rank a :< rank b.
Proof.
  intros a b H1.
  assert (Ordinal (rank a)) as G1. { apply IsOrdinal. }
  assert (Ordinal (rank b)) as G2. { apply IsOrdinal. }
  assert (Ordinal (succ (rank a))) as G3. { apply Succ.IsOrdinal. assumption. }
  apply Succ.ElemIsIncl; try assumption.
  apply IsLargest. 1: assumption.
  rewrite R1.WhenSucc. 2: assumption. intros H2.
  apply Power.Charac in H2.
  assert (a :< R1!(rank a)) as H3. { apply H2. assumption. }
  assert (~ a :< R1!(rank a)) as H4. { apply IsNotIn. 1: assumption. apply Incl.Refl. }
  contradiction.
Qed.

Proposition FromElems : forall (a:U),
  rank a = inf (fun b => Ordinal b /\ forall x, x :< a -> rank x :< b).
Proof.
  intros a.
  assert (Ordinal (rank a)) as G1. { apply IsOrdinal. }
  remember (fun b => Ordinal b /\ forall x, x :< a -> rank x :< b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. {
    apply CEM.HasElem. exists (rank a). rewrite H1. split. 1: assumption.
    intros x H3. apply ElemCompat. assumption. }
  apply DoubleInclusion. split.
  - apply SOI.IsLargest; try assumption. rewrite H1. intros b [H4 H5].
    assert (Ordinal (succ b)) as K1. { apply Succ.IsOrdinal. assumption. }
    apply Succ.InclIsElem; try assumption.
    apply IsLowerBound. 1: assumption.
    rewrite WhenSucc. 2: assumption. apply Power.Charac. intros x H6.
    assert (Ordinal (rank x)) as K2. { apply IsOrdinal. }
    assert (Ordinal (succ (rank x))) as K3. { apply Succ.IsOrdinal. assumption. }
    apply R1.InclCompat with (succ (rank x)); try assumption.
    + apply Succ.ElemIsIncl; try assumption. apply H5. assumption.
    + apply IsIn. 1: assumption. apply Succ.IsIn.
  - apply SOI.IsLowerBound. 1: assumption. rewrite H1. split. 1: assumption.
    intros x H4. apply ElemCompat. assumption.
Qed.

Proposition WhenOrdinal : forall (a:U), Ordinal a -> rank a = a.
Proof.
  apply COI.Induction.
  intros a H1 IH.
  remember (fun b => Ordinal b /\ forall c, c :< a -> rank c :< b) as A eqn:H2.
  remember (fun b => Ordinal b /\ a :<=: b) as B eqn:H3.
  assert (rank a = inf A) as H4. { rewrite H2. apply FromElems. }
  assert (A :~: B) as H5. {
    intros b. split; intros H5.
    - rewrite H2 in H5. destruct H5 as [H5 H6]. rewrite H3. split. 1: assumption.
      intros c H7. rewrite <- (IH c). 2: assumption. apply H6. assumption.
    - rewrite H3 in H5. destruct H5 as [H5 H6]. rewrite H2. split. 1: assumption.
      intros c H7. rewrite (IH c). 2: assumption. apply H6. assumption. }
  assert (inf A = inf B) as H6. { apply SOI.EquivCompat. assumption. }
  assert (B :<=: Ordinal) as H7. { rewrite H3. intros x H7. apply H7. }
  assert (B :<>: :0:) as H8. {
    apply CEM.HasElem. exists a. rewrite H3. split. 1: assumption.
    apply Incl.Refl. }
  assert (inf B = a) as H9. {
    apply Incl.DoubleInclusion. split.
    - apply SOI.IsLowerBound. 1: assumption. rewrite H3. split. 1: assumption.
      apply Incl.Refl.
    - apply SOI.IsLargest; try assumption. intros b H9.
      rewrite H3 in H9. apply H9. }
  rewrite H4, H6, H9. reflexivity.
Qed.

Proposition InclCompat : forall (a b:U),
  a :<=: b -> rank a :<=: rank b.
Proof.
  intros a b H1.
  assert (Ordinal (rank b)) as G1. { apply IsOrdinal. }
  remember (fun c => Ordinal c /\ forall x, x :< a -> rank x :< c) as A eqn:H2.
  remember (fun c => Ordinal c /\ forall x, x :< b -> rank x :< c) as B eqn:H3.
  assert (rank a = inf A) as H4. { rewrite H2. apply FromElems. }
  assert (rank b = inf B) as H5. { rewrite H3. apply FromElems. }
  assert (A :<=: Ordinal) as H6. { rewrite H2. intros x H6. apply H6. }
  assert (B :<>: :0:) as H7. {
    apply CEM.HasElem. exists (rank b). rewrite H3. split. 1: assumption.
    intros x H7. apply ElemCompat. assumption. }
  assert (B :<=: A) as H8. {
    rewrite H2, H3. intros c [H8 H9]. split. 1: assumption. intros x H10.
    apply H9, H1. assumption. }
  rewrite H4, H5. apply SOI.InclCompat; assumption.
Qed.
