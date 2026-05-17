Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.SuccOf.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.Union.

(* The class of limit ordinals.                                                 *)
Definition Limit : Class := Ordinal :\: NonLimit.

(* A limit ordinal cannot also be a non-limit ordinal.                          *)
Proposition NotBoth : forall (a:U),
  Limit a -> NonLimit a -> False.
Proof.
  intros a [H1 H2] H3. apply H2. assumption.
Qed.

(* A limit ordinal is not a successor ordinal.                                  *)
Proposition NotSucc : forall (a:U),
  Limit a -> ~ Successor a.
Proof.
  intros a H1 [b [H2 H3]]. apply NotBoth with a. 1: assumption.
  right. exists b. split; assumption.
Qed.

(* The successor of any set is not a limit ordinal.                             *)
Proposition SuccIsNot : forall (a:U),
  ~ Limit (succ a).
Proof.
  intros a H1.
  assert (Ordinal (succ a)) as H2. { apply H1. }
  assert (Ordinal a) as H3. {  apply IsOrdinalRev. assumption. }
  apply NotSucc with (succ a). 1: assumption.
  apply Succ.IsSuccessor. assumption.
Qed.

(* Limit is a class of ordinals.                                                *)
Proposition HasOrdinals : Limit :<=: Ordinal.
Proof.
  apply Class.Inter2.IsInclL.
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
      exists :U(a). split.
      1: { apply IsOrdinalRev. rewrite <- H3. assumption. }
      assumption.
  - destruct H2 as [H2 H3]. split. 1: assumption. intros [H4|H4].
    + contradiction.
    + destruct H4 as [b [H4 H5]].
      apply IfUnionThenNotSucc with a b; try assumption.
Qed.

(* Every limit ordinal contains zero.                                           *)
Proposition HasZero : forall (a:U),
  Limit a -> :0: :< a.
Proof.
  intros a H1.
  assert (Ordinal a) as H2. { apply H1. }
  apply Charac in H1. 2: assumption.
  apply Core.HasZero. 1: assumption. apply H1.
Qed.

(* 0 is not a limit ordinal.                                                    *)
Proposition NotZero : ~ Limit :0:.
Proof.
  intros H1.
  assert (:0: :< :0:) as H2. { apply HasZero. assumption. }
  apply Empty.Charac in H2. contradiction.
Qed.

(* A limit ordinal is not 0.                                                    *)
Proposition IsNotZero : forall (a:U), Limit a -> a <> :0:.
Proof.
  intros a H1 H2. subst. apply NotZero. assumption.
Qed.

(* A limit ordinal contains the successor of each of its elements.              *)
Proposition HasSucc : forall (a b:U),
  Limit a -> b :< a -> succ b :< a.
Proof.
  intros a b H1 H2. assert (Ordinal a) as H3. {
    apply HasOrdinals. assumption. }
    apply Charac in H1; try assumption.
  destruct H1 as [_ H1]. assert (H4 := H2). rewrite H1 in H4.
  apply Union.Charac in H4. destruct H4 as [c [H4 H5]].
  assert (Ordinal b) as H6. {
    apply Core.IsOrdinal with a; assumption. }
  assert (Ordinal c) as H7. {
    apply Core.IsOrdinal with a; assumption. }
  apply InclElemTran with c; try assumption.
  - apply Succ.IsOrdinal. assumption.
  - apply Succ.ElemIsIncl; assumption.
Qed.

(* Every limit ordinal contains 1.                                              *)
Proposition HasOne : forall (a:U),
  Limit a -> :1: :< a.
Proof.
  intros a H1. apply HasSucc. 1: assumption. apply HasZero. assumption.
Qed.

(* In a limit ordinal, every element has a strictly larger element.             *)
Proposition InBetween : forall (a b:U),
  Limit a -> b :< a -> exists c, b :< c /\ c :< a.
Proof.
  intros a b H1 H2. exists (succ b). split.
  - apply Succ.IsIn.
  - apply HasSucc; assumption.
Qed.

(* For a limit ordinal, inclusion of succ b in a implies membership.            *)
Proposition InclIsElem : forall (a b:U),
  Limit a -> Ordinal b -> succ b :<=: a -> succ b :< a.
Proof.
  intros a b H1 H2 H3.
  assert (Ordinal a) as H4. { apply H1. }
  assert (Ordinal (succ b)) as H5. { apply Succ.IsOrdinal. assumption. }
  assert (succ b = a \/ succ b :< a \/ a :< succ b) as H6. {
    apply Core.IsTotal; assumption. }
  destruct H6 as [H6|[H6|H6]]. 2: assumption.
  - exfalso. apply NotBoth with a. 1: assumption. right.
    exists b. split. 1: assumption. symmetry. assumption.
  - exfalso. apply Foundation.NoLoop1 with a. apply H3. assumption.
Qed.

(* Every ordinal is either zero, a successor ordinal, or a limit ordinal.       *)
Proposition ThreeWay : forall (a:U), Ordinal a ->
  a = :0: \/ Successor a \/ Limit a.
Proof.
  intros a H1.
  assert (NonLimit a \/ ~NonLimit a) as H2. { apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - apply NonLimit.Charac in H2. 2: assumption. destruct H2 as [H2|H2].
    + left. assumption.
    + right. left. rewrite H2.
      apply Succ.IsSuccessor, UnionOf.IsOrdinal. assumption.
  - right. right. split; assumption.
Qed.

(* Every positive ordinal is either a successor or a limit ordinal.             *)
Proposition TwoWay : forall (a:U), Ordinal a ->
  :0: :< a -> Successor a \/ Limit a.
Proof.
  intros a H1 H2.
  assert (a = :0: \/ Successor a \/ Limit a) as H3. {
    apply ThreeWay. assumption. }
  destruct H3 as [H3|H3]. 2: assumption.
  exfalso. subst. apply Empty.Charac in H2. contradiction.
Qed.

(* A non-zero ordinal closed under successor is a limit ordinal.                *)
Proposition WhenHasSucc : forall (a:U), Ordinal a ->
  a <> :0:                          ->
  (forall b, b :< a -> succ b :< a) ->
  Limit a.
Proof.
  intros a H1 H2 H3.
  assert (a = :0: \/ Successor a \/ Limit a) as H4. {
    apply ThreeWay. assumption. }
  destruct H4 as [H4|[H4|H4]]. 3: assumption. 1: contradiction. exfalso.
  assert (succ :U(a) :< succ :U(a)) as H5. { (* contradiction *)
    apply (Succ.OfUnion a H1) in H4. symmetry in H4.
    rewrite H4 in H3. apply H3, Succ.IsIn. }
  revert H5. apply Foundation.NoLoop1.
Qed.
