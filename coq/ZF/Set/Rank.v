Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.R1.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.
Require Import ZF.Set.WellFounded.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module CIN := ZF.Class.Incl.
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
  a :< R1!b -> succ(rank a) :<=: b.
Proof.
  intros a b H1 H2.
  assert (Ordinal (rank a)) as G1. { apply IsOrdinal. }
  assert (Ordinal (succ (rank a))) as G2. { apply Succ.IsOrdinal. assumption. }
  assert (b :< succ (rank a) \/ succ (rank a) :<=: b) as H3. {
    apply Core.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3]. 2: assumption.
  assert (succ b :<=: succ (rank a)) as H4. {
    apply Succ.ElemIsIncl; assumption. }
  assert (b :<=: rank a) as H5. { apply Succ.InclCompatRev; assumption. }
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

