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
Admitted.

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
