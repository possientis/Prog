Require Import ZF.Class.Complement.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.IsSetOf.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
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

Proposition IsIncl : forall (A:Class), upper A :<=: On.
Proof.
  intros A a [H1 _]. assumption.
Qed.

Proposition NotEmptyOn : forall (A:Class),
  upper A :<>: :0: <-> upper A :/\: On :<>: :0:.
Proof.
  intros A. split; intros H1; apply Class.Empty.HasElem in H1;
  destruct H1 as [a H1]; apply Class.Empty.HasElem; exists a.
  - split. 1: assumption. apply IsIncl with A. assumption.
  - destruct H1 as [H1 _]. assumption.
Qed.

(* An ordinal is an ordinal upper-bound iff it does not belong to the supremum. *)
Proposition NotInSup : forall (A:Class) (a:U), On a ->
  upper A a <-> ~ sup A a.
Proof.
  intros A a H1. split; intros H2.
  - destruct H2 as [H2 H3]. intros H4. apply NoElemLoop1 with a.
    apply Sup.IsSmallest with (A :/\: On).
    + apply Class.Inter2.IsInclR.
    + intros b [H5 H6]. apply H3; assumption.
    + apply Sup.InterOn in H4. assumption.
  - split. 1: assumption. intros b H3 H4.
    assert (
      sup A :~: toClass a \/ sup A :<: toClass a \/ toClass a :<: sup A) as H5. {
        apply Class.Ordinal.Core.OrdinalTotal.
        - apply Sup.IsOrdinal.
        - apply Class.Ordinal.Core.IsOrdinal with On.
          2: assumption. apply OnIsOrdinal. }
    destruct H5 as [H5|[H5|H5]].
    + intros x H6. apply H5. apply Sup.InterOn.
      apply (Sup.IsUpperBound (A :/\: On) b). 3: assumption.
      * apply Class.Inter2.IsInclR.
      * split; assumption.
    + intros x H6. apply H5. apply Sup.InterOn.
      apply (Sup.IsUpperBound (A :/\: On) b). 3: assumption.
      * apply Class.Inter2.IsInclR.
      * split; assumption.
    + apply Class.Ordinal.Core.LessIsElem in H5.
      * contradiction.
      * apply Sup.IsOrdinal.
      * apply Class.Ordinal.Core.IsOrdinal with On.
        2: assumption. apply OnIsOrdinal.
Qed.

(* The supremum is a small class iff there is an ordinal upper-bound.           *)
Proposition IsSmall : forall (A:Class),
  upper A :<>: :0: <-> Small (sup A).
Proof.
  intros A. split; intros H1.
  - apply Class.Empty.HasElem in H1. destruct H1 as [a H1].
    assert (sup A :~: On \/ Small (sup A)) as H2. { apply Sup.IsOnOrSmall. }
    destruct H2 as [H2|H2]. 2: assumption. exfalso. assert (H3 := H1).
    destruct H3 as [H3 _]. apply NotInSup in H1. 2: assumption.
    apply H1, H2. assumption.
  - assert (sup A :~: On \/ sup A :<: On) as H2. {
      apply Core.IsOnOrLess, Sup.IsOrdinal. }
    destruct H2 as [H2|H2].
    + exfalso. apply Core.OnIsProper, Small.EquivCompat with (sup A); assumption.
    + apply Diff.WhenLess in H2. apply Class.Empty.HasElem in H2.
      destruct H2 as [a [H2 H3]]. apply Class.Empty.HasElem. exists a.
      apply NotInSup; assumption.
Qed.

(* If the supremum is a set, it belongs to the class of ordinal upper-bounds.   *)
Proposition IsIn : forall (A:Class) (a:U),
  IsSetOf (sup A) a -> upper A a.
Proof.
  intros A a H1.
  assert (On a) as H2. {
    apply Class.Ordinal.Core.EquivCompat with (sup A).
    apply Equiv.Sym. assumption. apply Sup.IsOrdinal. }
  split. 1: assumption. intros b H3 H4. apply Incl.EquivCompatR with (sup A).
  - apply Equiv.Sym. assumption.
  - apply Sup.IsUpperBoundOrd; assumption.
Qed.

(* The supremum is the infimum of all ordinal upper-bounds (when these exist).  *)
Proposition IsInf : forall (A:Class), upper A :<>: :0: ->
  sup A :~: inf (upper A).
Proof.
  intros A H1.
  assert (Small (sup A)) as H2. { apply IsSmall. assumption. }
  assert (exists a, IsSetOf (sup A) a) as H3. { assumption. }
  destruct H3 as [a H3].
  assert (Small (inf (upper A))) as H4. { apply Inf.IsSmall. }
  assert (exists b, IsSetOf (inf (upper A)) b) as H5. { assumption. }
  destruct H5 as [b H5]. apply Class.Incl.DoubleInclusion. split.
  - apply Incl.EquivCompatR with (toClass b). 1: assumption.
    apply Sup.IsSmallestOrd. intros c H6 H7.
    apply Incl.EquivCompatR with (inf (upper A)).
    + apply Equiv.Sym. assumption.
    + apply Inf.IsLargestOrd.
      * apply NotEmptyOn. assumption.
      * intros d H8 H9. apply H9; assumption.
  - apply Incl.EquivCompatR with (toClass a). 1: assumption.
    assert (upper A a) as H10. { apply IsIn. assumption. }
    apply Inf.IsLowerBoundOrd. 2: assumption. apply IsIncl with A. assumption.
Qed.
