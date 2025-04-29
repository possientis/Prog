Require Import ZF.Class.Complement.
Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Union.

(* The class of limit ordinals.                                                 *)
Definition Limit : Class := Ordinal :\: NonLimit.

(* Limit is a class of ordinals.                                                *)
Proposition IsClassOfOrdinals : Limit :<=: Ordinal.
Proof.
  apply Class.Inter2.InclL.
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
      exists :U(a). split. 2: assumption. apply UnionOf.IsOrdinal.
      assumption.
  - destruct H2 as [H2 H3]. split. 1: assumption. intros [H4|H4].
    + contradiction.
    + destruct H4 as [b [H4 H5]]. apply IfUnionThenNotSucc with a b; assumption.
Qed.

Proposition HasSucc : forall (a b:U),
  Limit a -> b :< a -> succ b :< a.
Proof.
  intros a b H1 H2. assert (Ordinal a) as H3. {
    apply IsClassOfOrdinals. assumption. }
    apply Charac in H1; try assumption.
  destruct H1 as [_ H1]. assert (H4 := H2). rewrite H1 in H4.
  apply Union.Charac in H4. destruct H4 as [c [H4 H5]].
  assert (Ordinal b) as H6. {
    apply Core.IsOrdinal with a; assumption. }
  assert (Ordinal c) as H7. {
    apply Core.IsOrdinal with a; assumption. }
  apply InclElemTran with c; try assumption.
  - apply Succ.IsOrdinal. assumption.
  - apply ElemIsSuccIncl; assumption.
Qed.

Proposition InBetween : forall (a b:U),
  Limit a -> b :< a -> exists c, b :< c /\ c :< a.
Proof.
  intros a b H1 H2. exists (succ b). split.
  - apply Succ.IsIn.
  - apply HasSucc; assumption.
Qed.

(* The set N is a limit ordinal.                                                *)
Proposition NIsLimit : Limit :N.
Proof.
  split.
  - apply NIsOrdinal.
  - intros H1. apply NoElemLoop1 with :N. apply Omega.Charac. split.
    + apply NIsOrdinal.
    + intros n H2. apply Union2.Charac in H2. destruct H2 as [H2|H2].
      * apply IsNonLimit. assumption.
      * apply Single.Charac in H2. subst. assumption.
Qed.

(* A limit ordinal is no less than N.                                           *)
Proposition NoLessThanN : forall (a:U), Limit a -> :N :<=: a.
Proof.
  intros a H1. assert (a :< :N \/ :N :<=: a) as H2. {
    apply ElemOrIncl.
    - apply IsClassOfOrdinals. assumption.
    - apply NIsOrdinal. }
  destruct H2 as [H2|H2]. 2: assumption. exfalso.
  apply H1. apply Omega.Charac in H2. apply H2, Succ.IsIn.
Qed.
