Require Import ZF.Class.Complement.
Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.NonLimit.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Union.

(* The class of limit ordinals.                                                 *)
Definition Limit : Class := On :\: NonLimit.

(* Limit is a class of ordinals.                                                *)
Proposition LimitIsOrdinal : Limit :<=: On.
Proof.
  apply Inter.InclL.
Qed.

(* An ordinal is a limit ordinal iff it is not empty and is equal to its union. *)
Proposition NonEmptyAndUnion : forall (a:U), Ordinal a ->
  Limit a <-> a <> :0: /\ a = :U(a).
Proof.
  intros a H1. assert (a = :U(a) \/ a = succ :U(a)) as H2. {
    apply UnionOrSuccOfUnion. assumption. }
  split; intros H3.
  - split.
    + intros H4. apply H3. left. assumption.
    + destruct H2 as [H2|H2]. 1: assumption. exfalso. apply H3. right.
      exists :U(a). split. 2: assumption. apply UnionOfOrdinalIsOrdinal.
      assumption.
  - split. 1: assumption. intros H4. destruct H4 as [H4|H4].
    + destruct H3 as [H3 _]. contradiction.
    +
Admitted.

