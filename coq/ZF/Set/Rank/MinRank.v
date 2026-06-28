Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Rank.MinRank.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Rank.OfMinRank.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Rank.Core.


Module CMR := ZF.Class.Rank.MinRank.
Module SRC := ZF.Set.Rank.Core.

(* The minimal rank of the elements of A.                                       *)
Definition minRank (A:Class) : U := fromClass (CMR.minRank A) (CMR.IsSmall A).

(* The class of the minimal rank equals the corresponding class.                *)
Proposition ToClass : forall (A:Class),
  toClass (minRank A) :~: CMR.minRank A.
Proof.
  intros A x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* x belongs to the minimal rank iff it lies below a minimal element rank.      *)
Proposition Charac : forall (A:Class) (x:U),
  x :< minRank A <-> exists y, y :< ofMinRank A /\ x :< rank y.
Proof.
  apply ToClass.
Qed.

(* If A is empty, then its minimal rank is empty.                               *)
Proposition WhenZero : forall (A:Class),
  A :~: :0: -> minRank A = :0:.
Proof.
  intros A H1.
  apply Empty.EmptyToClass, Equiv.Tran with (CMR.minRank A).
  - apply ToClass.
  - apply CMR.WhenZero. assumption.
Qed.

(* The minimal rank is the rank of any minimal-rank element of A.               *)
Proposition Equal : forall (A:Class) (y:U),
  y :< ofMinRank A -> minRank A = rank y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A y H1. apply EqualToClass. intros x. split; intros H2.
  - apply Charac in H2. destruct H2 as [z [H2 H3]].
    assert (rank z = rank y) as H4. {
      apply OfMinRank.SameRank with A; assumption. }
    rewrite H4 in H3. assumption.
  - apply Charac. exists y. split; assumption.
Qed.

(* The minimal rank of any class is an ordinal.                                 *)
Proposition IsOrdinal : forall (A:Class), Ordinal (minRank A).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A.
  assert (A :~: :0: \/ A :<>: :0:) as [H1|H1]. { apply LawExcludedMiddle. }
  - rewrite WhenZero. 2: assumption. apply Core.Zero.
  - assert (ofMinRank A <> :0:) as H2. {
      apply OfMinRank.IsNotEmpty. assumption. }
    apply Empty.HasElem in H2. destruct H2 as [y H2].
    rewrite (Equal A y). 2: assumption. apply SRC.IsOrdinal.
Qed.

(* A non-empty class has an element whose rank is the minimal rank.             *)
Proposition IsAttained : forall (A:Class),
  A :<>: :0: -> exists y, A y /\ minRank A = rank y.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A H1.
  assert (ofMinRank A <> :0:) as H2. {
    apply OfMinRank.IsNotEmpty. assumption. }
  apply Empty.HasElem in H2. destruct H2 as [y H2].
  exists y. split.
  - apply OfMinRank.IsIncl. assumption.
  - apply Equal. assumption.
Qed.

(* The minimal rank is below the rank of every element of A.                    *)
Proposition IsLowerBound : forall (A:Class) (x:U),
  A x -> minRank A :<=: rank x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A x H1.
  assert (A :<>: :0:) as H2. { apply Class.Empty.HasElem. exists x. assumption. }
  assert (ofMinRank A <> :0:) as H3. {
    apply OfMinRank.IsNotEmpty. assumption. }
  apply Empty.HasElem in H3. destruct H3 as [y H3].
  assert (minRank A = rank y) as H4. { apply Equal. assumption. }
  rewrite H4.
  apply (OfMinRank.Charac A y). 1: assumption. assumption.
Qed.

(* The minimal rank is the largest lower bound of the ranks of elements of A.   *)
Proposition IsLargest : forall (A:Class) (b:U),
  A :<>: :0:                          ->
  Ordinal b                           ->
  (forall x, A x -> b :<=: rank x)    ->
  b :<=: minRank A.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A b H1 H2 H3.
  assert (exists y, A y /\ minRank A = rank y) as H4. {
    apply IsAttained. assumption. }
  destruct H4 as [y [H4 H5]]. rewrite H5. apply H3. assumption.
Qed.

(* An element has minimal rank in A iff its rank is the minimal rank.           *)
Proposition OfCharac : forall (A:Class) (x:U),
  x :< ofMinRank A <-> A x /\ minRank A = rank x.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros A x. split; intros H1.
  - split.
    + apply OfMinRank.IsIncl. assumption.
    + apply Equal. assumption.
  - destruct H1 as [H1 H2]. apply OfMinRank.Charac. split. 1: assumption.
    intros y H3. rewrite <- H2. apply IsLowerBound. assumption.
Qed.

(* If A contains the empty set, then its minimal rank is empty.                 *)
Proposition WhenHasZero : forall (A:Class),
  A :0: -> minRank A = :0:.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* The minimal rank is below rank zero, and rank zero is zero.                *)
  intros A H1.
  assert ((minRank A) :<=: rank :0:) as H2. { apply IsLowerBound. assumption. }
  rewrite SRC.WhenOrdinal in H2. 2: apply Core.Zero.
  apply Empty.WhenIncl. assumption.
Qed.
