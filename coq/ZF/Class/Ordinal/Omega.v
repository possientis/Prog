Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Infinity.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.N.
Export ZF.Notation.N.

(* The class natural numbers.                                                   *)
Definition omega : Class := fun a =>
  Ordinal a /\ toClass (succ a) :<=: NonLimit.

(* Notation ":N" := omega                                                       *)
Global Instance ClassN : N Class := { omega := omega }.

(* N is a class of ordinals.                                                    *)
Proposition HasOrdinalElem : :N :<=: On.
Proof.
  intros a [H1 _]. assumption.
Qed.

(* N is a class of non-limit ordinals.                                          *)
Proposition HasNonLimitElem : :N :<=: NonLimit.
Proof.
  intros a [H1 H2]. apply H2. apply Succ.IsIn.
Qed.

(* 0 belongs to N. The type annotation is needed here for instance resolution.  *)
Proposition HasZero : (:N : Class) :0:.
Proof.
  split.
  - apply ZeroIsOrdinal.
  - intros a H1. apply Union2.Charac in H1. destruct H1 as [H1|H1].
    + apply Empty.Charac in H1. contradiction.
    + apply Single.Charac in H1. subst. left. reflexivity.
Qed.

(* If a is a natural number, then so is succ a.                                 *)
Proposition HasSucc : forall (a:U), (:N : Class) a -> (:N : Class) (succ a).
Proof.
  intros a [H1 H2]. split.
  - apply Succ.IsOrdinal. assumption.
  - intros b H3. apply Union2.Charac in H3. destruct H3 as [H3|H3].
    + apply H2. assumption.
    + apply Single.Charac in H3. subst. right. exists a. split.
      * assumption.
      * reflexivity.
Qed.

(* N is not an empty class.                                                     *)
Proposition IsNotEmpty : :N :<>: :0:.
Proof.
  intros H1. apply Class.Empty.Charac with :0:. apply H1, HasZero.
Qed.

(* Characterisation of the elements of N.                                       *)
Proposition Charac : forall (a:U), Ordinal a ->
  :N a <-> forall (b:U), Ordinal b -> b :<=: a -> NonLimit b.
Proof.
  intros a H1. split; intros H2.
  - destruct H2 as [H2 H3]. intros b H4 H5. apply H3.
    apply InclElemTran with a; try assumption.
    + apply Succ.IsOrdinal. assumption.
    + apply Succ.IsIn.
  - split. 1: assumption. intros b H3. assert (Ordinal b) as H4. {
      apply Core.IsOrdinal with (succ a). 2: assumption.
      apply Succ.IsOrdinal. assumption. }
    apply H2. 1: assumption.
    assert (a :< b \/ b :<=: a) as H5. { apply ElemOrIncl; assumption. }
    destruct H5 as [H5|H5]. 2: assumption.
    exfalso. apply NoInBetween with a b. split; assumption.
Qed.

(* An ordinal with non-limit ordinals as elements is a subclass of N.           *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  toClass a :<=: NonLimit -> toClass a :<=: :N.
Proof.
  intros a H1 H2 b H3. split.
  - apply Core.IsOrdinal with a; assumption.
  - intros c H4. assert (Ordinal b) as H5. {
      apply Core.IsOrdinal with a; assumption. }
    assert (Ordinal c) as H6. {
      apply Core.IsOrdinal with (succ b). 2: assumption.
      apply Succ.IsOrdinal. assumption. }
    apply H2. apply InclElemTran with b; try assumption.
    apply InclCompatRev; try assumption.
    apply Succ.ElemIsIncl; try assumption.
    apply Succ.IsOrdinal. assumption.
Qed.

(* Principle of induction over the natural numbers.                             *)
Proposition Induction : forall (A:Class),
  A :0:                                           ->
  (forall n, (:N : Class) n -> A n -> A (succ n)) ->
  :N :<=: A.
Proof.
  intros A H1 H2. apply Diff.WhenEmpty, DoubleNegation. intros H3.
  assert (:N :\: A :<=: On) as H4. {
    apply Class.Incl.Tran with :N.
    - apply Class.Inter2.IsInclL.
    - apply HasOrdinalElem. }
  assert (exists n,
    Ordinal n                       /\
    (:N :\: A) n                    /\
    forall m, (:N :\: A) m -> n :<=: m ) as H5. {
      apply HasMinimal; assumption. }
  destruct H5 as [n [H5 [[H6 H7] H8]]].
  assert (n <> :0:) as H9. { intros H9. subst. contradiction. }
  assert (NonLimit n) as H10. { apply HasNonLimitElem. assumption. }
  destruct H10 as [H10|H10]. 1: contradiction.
  destruct H10 as [b [H10 H11]]. assert (H12 := H6). destruct H12 as [_ H12].
  assert ((:N : Class) b) as H13. { split. 1: assumption.
    apply Class.Incl.Tran with (toClass (succ n)). 2: assumption.
      rewrite <- H11. apply Succ.IsIncl. }
  assert (~ (:N :\: A) b) as H14. { intros H14. apply H8 in H14.
    apply NoElemLoop1 with b. apply H14. rewrite H11. apply Succ.IsIn. }
  apply H7. rewrite H11. apply H2. 1: assumption. apply DoubleNegation.
  intros H15. apply H14. split; assumption.
Qed.

(* Principle of induction over the natural numbers.                             *)
Proposition FiniteInduction : forall (A:Class),
  A :<=: :N                     ->
  A :0:                         ->
  (forall n, A n -> A (succ n)) ->
  A :~: :N.
Proof.
  intros A H1 H2 H3. apply DoubleInclusion. split. 1: assumption.
  apply Induction. 1: assumption. intros n _. apply H3.
Qed.

(* N is a transitive class.                                                     *)
Proposition IsTransitive : Transitive :N.
Proof.
  intros b H1 a H2. assert (H3 := H1). destruct H3 as [H3 H4].
  assert (Ordinal a) as H5. { apply Core.IsOrdinal with b; assumption. }
  assert (toClass (succ a) :<=: NonLimit) as H6. {
    intros x H7. apply Union2.Charac in H7. destruct H7 as [H7|H7].
    - apply H4, Succ.IsIncl. apply (IfElemThenIncl a b); assumption.
    - apply Single.Charac in H7. subst. apply H4, Succ.IsIncl. assumption. }
  split; assumption.
Qed.

(* N is an ordinal class.                                                       *)
Proposition IsOrdinal : Class.Ordinal.Core.Ordinal :N.
Proof.
  split. 1: apply IsTransitive. intros a b [H1 _] [H2 _].
  apply OrdinalTotal; assumption.
Qed.

(* The class N is in fact small, thanks to the axiom of infinity.               *)
Proposition IsSmall : Small :N.
Proof.
  (* We need to show that N is small. *)
  assert (Small :N) as X. 2: apply X.

  (* There is a set containing 0 and the successor of all its elements. *)
  assert (exists a,
    :0: :< a /\ forall x, x :< a -> succ x :< a) as H1. {apply Infinity. }

  (* So let a be such a set. *)
  destruct H1 as [a [H1 H2]].

  (* Then 0 :< a. *)
  assert (:0: :< a) as X. apply H1. clear X.

  (* And succ x :< a when x :< a. *)
  assert (forall x, x :< a -> succ x :< a) as X. apply H2. clear X.

  (* We prove N is small by showing it is bounded. *)
  apply Bounded.IsSmall.

  (* So we need to show the existence of a set a such that N <= a. *)
  assert (exists a, :N :<=: toClass a) as X. 2: apply X.

  (* We claim our set a is such a set. *)
  exists a.

  (* So we need to show that N <= a. *)
  assert (:N :<=: toClass a) as X. 2: apply X.

  (* We proceed by induction. *)
  apply Induction.

  (* We first need to show that :0: :< a. *)
  - assert (:0: :< a) as X. 2: apply X.

  (* Which is true. *)
    apply H1.

  (* And we need to show that for all i in N, i :< a -> succ i :< a. *)
  - assert (forall i, (:N : Class) i -> i :< a -> succ i :< a) as X. 2: apply X.

  (* Which is also true. *)
    intros i _. apply H2.
Qed.
