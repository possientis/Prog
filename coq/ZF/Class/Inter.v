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

(* The class of sets x which belong to all elements of P.                       *)
Definition inter (P:Class) : Class := fun x =>
  forall y, P y -> x :< y.

(* Notation ":I( P )" := (inter P)                                              *)
Global Instance ClassInter : Inter Class := { inter := inter }.

(* Tweak which reduces the class to 0 when P is empty.                          *)
Definition inter' (P:Class) : Class := fun x =>
  :I(P) x /\ exists y, P y.

(* Notation ":J( P )" := (inter' P)                                             *)
Global Instance ClassInter' : Inter' Class := { inter' := inter' }.

(* The class J(P) reduces to 0 when P is empty.                                 *)
Proposition WhenEmpty : forall (P:Class),
  P :~: :0: -> :J(P) :~: :0:.
Proof.
  intros P H1 a. split; intros H2.
  - destruct H2 as [H2 [b H3]]. exfalso.
    apply Class.Empty.Charac with b. apply H1. assumption.
  - contradiction.
Qed.

(* The class J(P) coincides with I(P) when P is not empty.                      *)
Proposition WhenNotEmpty : forall (P:Class),
  P :<>: :0: -> :J(P) :~: :I(P).
Proof.
  intros P H1 x. split; intros H2.
  - apply H2.
  - split. 1: assumption. apply Class.Empty.HasElem in H1. assumption.
Qed.

(* The intersection is compatible with class equivalence.                       *)
Proposition EquivCompat : forall (P Q:Class),
  P :~: Q -> :I(P) :~: :I(Q).
Proof.
  intros P Q H1 x. split; intros H2 y H3; apply H2, H1; assumption.
Qed.

(* The (tweaked) intersection is compatible with class equivalence.             *)
Proposition EquivCompat' : forall (P Q:Class),
  P :~: Q -> :J(P) :~: :J(Q).
Proof.
  intros P Q H1 x. split; intros [H2 H3]; split.
  - apply EquivCompat with P. 2: assumption. apply EquivSym. assumption.
  - destruct H3 as [a H3]. exists a. apply H1. assumption.
  - apply EquivCompat with Q; assumption.
  - destruct H3 as [a H3]. exists a. apply H1. assumption.
Qed.

(* The intersection of P is a subclass of all elements of P.                    *)
Proposition IsIncl : forall (P:Class) (a:U),
  P a -> :I(P) :<=: toClass a.
Proof.
  intros P a H1 x H2. apply H2. assumption.
Qed.

(* The intersection of P is small when P is not empty.                          *)
Proposition IsSmall : forall (P:Class), P :<>: :0: -> Small :I(P).
Proof.
  intros P H1. apply Class.Empty.HasElem in H1. destruct H1 as [a H1].
  apply Bounded.IsSmall. exists a. apply IsIncl. assumption.
Qed.

(* The (tweaked) intersection of P is small.                                    *)
Proposition IsSmall' : forall (P:Class), Small :J(P).
Proof.
  intros P. assert (P :~: :0: \/ P :<>: :0:) as H1. {
    apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - apply Small.EquivCompat with :0:.
    + apply EquivSym, WhenEmpty. assumption.
    + apply Small.EquivCompat with (toClass :0:).
      * apply ZF.Set.Empty.ToClass.
      * apply SetIsSmall.
  - apply Small.EquivCompat with :I(P).
    + apply EquivSym, WhenNotEmpty. assumption.
    + apply IsSmall. assumption.
Qed.

(* The intersection of a pair is the binary intersection of its elements.       *)
Proposition InterOfPair : forall (a b:U),
  :I(toClass :{a,b}:) :~: toClass (a :/\: b).
Proof.
  intros a b x. split; intros H1.
  - apply Inter2.Charac. split; apply H1.
    + apply Pair.IsInL.
    + apply Pair.IsInR.
  - apply Inter2.Charac in H1. destruct H1 as [H1 H2]. intros y H3.
    apply Pair.Charac in H3. destruct H3 as [H3|H3]; subst; assumption.
Qed.

Proposition IsZero : :J(:0:) :~: :0:.
Proof.
  apply WhenEmpty, EquivRefl.
Qed.
