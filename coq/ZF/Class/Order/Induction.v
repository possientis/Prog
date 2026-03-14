Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.TranClosure.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Module CIT := ZF.Class.Inter2.
Module COI := ZF.Class.Order.InitSegment.

Proposition Induction1 : forall (R A B:Class),
  WellFounded R A                                     ->
  B :<=: A                                            ->
  (forall x, A x -> initSegment R A x :<=: B -> B x)  ->
  A :~: B.
Proof.

  (* Let R A B be arbitrary classes. *)
  intros R A B.

  (* We assume that R is a well-founded well-ordering on A. *)
  intros H1. assert (WellFounded R A) as X. apply H1. clear X.

  (* We assume that B is a subclass of A. *)
  intros H2. assert (B :<=: A) as X. apply H2. clear X.

  (* We assume the inductive property. *)
  intros H3.
  assert (forall x, A x -> initSegment R A x :<=: B -> B x) as X. apply H3. clear X.

  (* We need to show that A = B. *)
  assert (A :~: B) as X. 2: apply X.

  (* It is sufficient to show that A <= B. *)
  apply DoubleInclusion. split. 2: assumption. assert (A :<=: B) as X. 2: apply X.

  (* Or equivalently that A\B = 0. *)
  apply Diff.WhenEmpty. assert (A:\:B :~: :0:) as X. 2: apply X.

  (* Suppose to the contrary that A\B <> 0. *)
  apply DoubleNegation. intros H5. assert (~ A:\:B :~: :0:) as X. apply H5. clear X.

  (* Then A\B has an R-minimal element. *)
  assert (exists a, Minimal R (A:\:B) a) as H6. {
    apply TranClosure.HasMinimal with A.
    - assumption.
    - apply Class.Inter2.IsInclL.
    - assumption.
  }

  (* So let a be such an R-minimal element. *)
  destruct H6 as [a H6]. assert (Minimal R (A:\:B) a) as X. apply H6. clear X.

  (* So the initial segment in A at a must be inside B. *)
  assert (initSegment R A a :<=: B) as H7. {
    intros x H7. apply COI.Charac in H7. destruct H7 as [H7 H8].
    apply DoubleNegation. intros H9. revert H8.
    apply H6. split; assumption. }

  (* From the inductive property, it follows that a lies in B. *)
  assert (B a) as H8. {
    apply H3. 2: assumption. apply Minimal.IsIn in H6.
    destruct H6 as [H6 _]. assumption. }

  (* This contradicts the fact that a lies in A\B. *)
  apply Minimal.IsIn in H6. destruct H6 as [_ H6]. contradiction.
Qed.


Proposition Induction : forall (R A B:Class),
  WellFounded R A                                                   ->
  (forall a, A a -> (forall x, initSegment R A a x -> B x) -> B a)  ->
   forall a, A a -> B a.
Proof.
  intros R A B H1 H2.
  assert (A :~: A :/\: B) as H3. {
    apply Induction1 with R. 1: assumption.
    - apply CIT.IsInclL.
    - intros a H3 H4. split. 1: assumption. apply H2. 1: assumption.
      intros x H5. apply H4. assumption. }
  intros a H4. apply H3. assumption.
Qed.

