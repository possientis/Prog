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
Proposition IsOrdinal : Limit :<=: On.
Proof.
  apply Class.Inter.InclL.
Qed.

(* An ordinal is a limit ordinal iff it is not empty and is equal to its union. *)
Proposition Charac : forall (a:U), Ordinal a ->
  Limit a <-> a <> :0: /\ a = :U(a).
Proof.
  intros a H1. split; intros H2.
  - split.
    + intros H3. apply H2. left. assumption.
    + assert (a = :U(a) \/ a = succ :U(a)) as H3. {
        apply UnionOrSuccOfUnion. assumption. }
      destruct H3 as [H3|H3]. 1: assumption. exfalso. apply H2. right.
      exists :U(a). split. 2: assumption. apply UnionOfOrdinalIsOrdinal.
      assumption.
  - destruct H2 as [H2 H3]. split. 1: assumption. intros [H4|H4].
    + contradiction.
    + destruct H4 as [b [H4 H5]]. apply IfUnionThenNotSucc with a b; assumption.
Qed.

