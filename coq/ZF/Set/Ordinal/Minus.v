Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.

Require Import ZF.Notation.Minus.
Export ZF.Notation.Minus.

(* b - a is the smallest ordinal c such that b <= a + c.                        *)
Definition minus (b a:U) : U := inf :{ succ b | fun c => b :<=: a :+: c }:.

(* Notation "b :-: a" := (minus b a)                                            *)
Global Instance SetMinus : Minus U := { minus := minus }.

Proposition IsOrdinal : forall (a b:U), Ordinal (a :-: b).
Proof.
  intros a b. apply Inf.IsOrdinal.
Qed.

Proposition IsEqual : forall (a b:U), Ordinal a -> Ordinal b  ->
  a :<=: b -> a :+: (b :-: a) = b.
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal (succ b)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (exists c, Ordinal c /\ a :+: c = b) as H4. {
    apply Plus.CompleteR; assumption. }
  destruct H4 as [c [H4 H5]].
  assert (b :<=: a :+: (b :-: a)) as H6. {
    remember (:{ succ b | fun c => b :<=: a :+: c }:) as G eqn:H6.
    assert (b :-: a = inf G) as H7. { rewrite H6. reflexivity. }
    assert (toClass G :<=: Ordinal) as H8. {
      intros d H8. rewrite H6 in H8. apply Specify.Charac in H8.
      destruct H8 as [H8 H9].
      apply Core.IsOrdinal with (succ b); assumption. }
    assert (G <> :0:) as H9. {
      apply Empty.HasElem. exists c. rewrite H6.
      apply Specify.Charac. split.
      - apply Core.InclElemTran with b; try assumption. 2: apply Succ.IsIn.
        rewrite <- H5. apply Plus.IsInclAddL; assumption.
      - rewrite H5. apply Incl.Refl. }
    assert (b :-: a :< G) as H10. {
      rewrite H7. apply Inf.IsIn; assumption. }
      rewrite H6 in H10. apply Specify.Charac in H10. apply H10. }
  assert (a :+: (b :-: a) :<=: b) as H7. {
    assert (Ordinal (b :-: a)) as H7. { apply IsOrdinal; assumption. }
    remember (b :-: a) as d eqn:H8. rewrite <- H5.
    rewrite H8. rewrite H8 in H6. rewrite H8 in H7. clear H8. clear d.
    apply Plus.InclCompatR; try assumption.
    apply Inf.IsLowerBound.
    - intros d H9. apply Specify.Charac in H9. destruct H9 as [H9 H10].
      apply Core.IsOrdinal with (succ b). 2: assumption.
      apply Succ.IsOrdinal. assumption.
    - apply Specify.Charac. split.
      + apply InclElemTran with b; try assumption.
        { rewrite <- H5. apply Plus.IsInclAddL; assumption. }
        { apply Succ.IsIn. }
      + rewrite H5. apply Incl.Refl. }
  apply DoubleInclusion. split; assumption.
Qed.

