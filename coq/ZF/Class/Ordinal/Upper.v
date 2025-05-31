Require Import ZF.Class.Complement.
Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Sup.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.

(* The class of ordinal upper-bounds of A.                                      *)
Definition upper (A:Class) : Class := fun a =>
  On a /\ forall b, On b -> A b -> b :<=: a.

(* Restricting a class to its ordinal elements leads to the same upper class.   *)
Proposition InterOn : forall (A:Class), upper A :~: upper (A :/\: On).
Proof.
  intros A x. split; intros [H1 H2]; split; try assumption; intros b H3 H4.
  - apply H2. 1: assumption. apply H4.
  - apply H2. 1: assumption. split; assumption.
Qed.

(* An ordinal is an ordinal upper-bound iff it does not belong to the supremum. *)
Proposition Charac : forall (A:Class) (a:U), On a ->
  upper A a <-> ~ sup A a.
Proof.
  intros A a H1. split; intros H2.
  - destruct H2 as [H2 H3]. intros H4. apply NoElemLoop1 with a.
    apply Sup.IsSmallest with (A :/\: On).
    + apply Inter2.IsInclR.
    + intros b [H5 H6]. apply H3; assumption.
    + apply Sup.InterOn in H4. assumption.
  - split. 1: assumption. intros b H3 H4.
    assert (
      sup A :~: toClass a \/ sup A :<: toClass a \/ toClass a :<: sup A) as H5. {
        apply Core.OrdinalTotal.
        - apply Sup.IsOrdinal.
        - apply Core.IsOrdinal with On. 2: assumption. apply OnIsOrdinal. }
    destruct H5 as [H5|[H5|H5]].
    + intros x H6. apply H5. apply Sup.InterOn.
      apply (Sup.IsUpperBound (A :/\: On) b). 3: assumption.
      * apply Inter2.IsInclR.
      * split; assumption.
    + intros x H6. apply H5. apply Sup.InterOn.
      apply (Sup.IsUpperBound (A :/\: On) b). 3: assumption.
      * apply Inter2.IsInclR.
      * split; assumption.
    + apply Core.LessIsElem in H5.
      * contradiction.
      * apply Sup.IsOrdinal.
      * apply Core.IsOrdinal with On. 2: assumption. apply OnIsOrdinal.
Qed.

(* The supremum is a small class iff there is an ordinal upper-bound.           *)
Proposition IsSmall : forall (A:Class),
  upper A :<>: :0: <-> Small (sup A).
Proof.
  intros A. split; intros H1.
  - apply Class.Empty.HasElem in H1. destruct H1 as [a H1].
    assert (sup A :~: On \/ Small (sup A)) as H2. { apply Sup.IsOnOrSmall. }
    destruct H2 as [H2|H2]. 2: assumption. exfalso. assert (H3 := H1).
    destruct H3 as [H3 _]. apply Charac in H1. 2: assumption.
    apply H1, H2. assumption.
  - assert (sup A :~: On \/ sup A :<: On) as H2. {
      apply Core.IsOnOrLess, Sup.IsOrdinal. }
    destruct H2 as [H2|H2].
    + exfalso. apply Core.OnIsProper, Small.EquivCompat with (sup A); assumption.
    + apply Diff.WhenLess in H2. apply Class.Empty.HasElem in H2.
      destruct H2 as [a [H2 H3]]. apply Class.Empty.HasElem. exists a.
      apply Charac; assumption.
Qed.


