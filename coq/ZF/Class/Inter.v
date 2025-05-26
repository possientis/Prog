Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Pair.

Require Import ZF.Notation.Inter.
Export ZF.Notation.Inter.

(* inter A is the empty class if A is empty, and otherwise is the class of all  *)
(* sets x which belong to all elements of A. We could define the intersection   *)
(* as being the whole universe of sets in the empty case, but this creates an   *)
(* issue, namely that the intersection cannot always be viewed as a set.        *)
Definition inter (A:Class) : Class := fun x =>
  (forall y, A y -> x :< y) /\ exists y, A y.

(* A more natural definition but less useful.                                   *)
Definition inter' (A:Class) : Class := fun x =>
  (forall y, A y -> x :< y).

(* Notation ":I( A )" := (inter A)                                              *)
Global Instance ClassInter : Inter Class := { inter := inter }.

(* The class I(A) reduces to 0 when A is empty.                                 *)
Proposition WhenEmpty : forall (A:Class),
  A :~: :0: -> :I(A) :~: :0:.
Proof.
  intros A H1 a. split; intros H2.
  - destruct H2 as [H2 [b H3]]. exfalso.
    apply Class.Empty.Charac with b. apply H1. assumption.
  - contradiction.
Qed.

Proposition IsZero : :I(:0:) :~: :0:.
Proof.
  apply WhenEmpty, EquivRefl.
Qed.

(* The class I(A) coincides with inter' A when A is not empty.                  *)
Proposition WhenNotEmpty : forall (A:Class),
  A :<>: :0: -> :I(A) :~: inter' A.
Proof.
  intros A H1 x. split; intros H2.
  - unfold inter'. apply H2.
  - split. 1: assumption. apply Class.Empty.HasElem in H1. assumption.
Qed.

(* The intersection inter' is compatible with class equivalence.                *)
Proposition EquivCompat' : forall (A B:Class),
  A :~: B-> inter' A :~: inter' B.
Proof.
  intros A B H1 x. split; intros H2 y H3; apply H2, H1; assumption.
Qed.

(* The intersection is compatible with class equivalence.                       *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> :I(A) :~: :I(B).
Proof.
  intros A B H1 x. split; intros [H2 H3]; split.
  - apply EquivCompat' with A. 2: assumption. apply EquivSym. assumption.
  - destruct H3 as [a H3]. exists a. apply H1. assumption.
  - apply EquivCompat' with B; assumption.
  - destruct H3 as [a H3]. exists a. apply H1. assumption.
Qed.

(* The intersection inter' A is a subclass of all elements of A.                *)
Proposition IsIncl' : forall (A:Class) (a:U),
  A a -> inter' A :<=: toClass a.
Proof.
  intros P a H1 x H2. apply H2. assumption.
Qed.

(* The intersection inter' A is small when A is not empty.                      *)
Proposition IsSmall' : forall (A:Class), A :<>: :0: -> Small (inter' A).
Proof.
  intros A H1. apply Class.Empty.HasElem in H1. destruct H1 as [a H1].
  apply Bounded.IsSmall. exists a. apply IsIncl'. assumption.
Qed.

(* The intersection of A is small.                                              *)
Proposition IsSmall : forall (A:Class), Small :I(A).
Proof.
  intros A. assert (A :~: :0: \/ A :<>: :0:) as H1. {
    apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - apply Small.EquivCompat with :0:.
    + apply EquivSym, WhenEmpty. assumption.
    + apply Small.EquivCompat with (toClass :0:).
      * apply ZF.Set.Empty.ToClass.
      * apply SetIsSmall.
  - apply Small.EquivCompat with (inter' A).
    + apply EquivSym, WhenNotEmpty. assumption.
    + apply IsSmall'. assumption.
Qed.

(* The intersection of a pair is the binary intersection of its elements.       *)
Proposition Pair : forall (a b:U),
  :I(toClass :{a,b}:) :~: toClass (a :/\: b).
Proof.
  intros a b x. split; intros H1.
  - apply Inter2.Charac. split; apply H1.
    + apply Pair.IsInL.
    + apply Pair.IsInR.
  - apply Inter2.Charac in H1. destruct H1 as [H1 H2]. split.
    + intros y H3.
      apply Pair.Charac in H3. destruct H3 as [H3|H3]; subst; assumption.
    + exists a. apply Pair.IsInL.
Qed.
