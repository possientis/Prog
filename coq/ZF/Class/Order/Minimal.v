Require Import ZF.Class.Core.
Require Import ZF.Class.Bij.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Set.Core.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that a is an R-minimal element of A.           *)
Definition Minimal (R A:Class) (a:U) : Prop
  := A a /\ initSegment R A a :~: :0:.

Proposition MinimalEquivCompat : forall (R S A B:Class) (a:U),
  R :~: S -> A :~: B -> Minimal R A a -> Minimal S B a.
Proof.
  intros R S A B a H1 H2 [H3 H4]; split.
  - apply H2. assumption.
  - apply EquivTran with (initSegment R A a). 2: assumption.
    apply EquivSym, InitSegmentEquivCompat; assumption.
Qed.

Proposition MinimalEquivCompatL : forall (R S A:Class) (a:U),
  R :~: S -> Minimal R A a -> Minimal S A a.
Proof.
  intros R S A a H1. apply MinimalEquivCompat.
  - assumption.
  - apply EquivRefl.
Qed.

Proposition MinimalEquivCompatR : forall (R A B:Class) (a:U),
  A :~: B -> Minimal R A a -> Minimal R B a.
Proof.
  intros R A B a H1. apply MinimalEquivCompat.
  - apply EquivRefl.
  - assumption.
Qed.

Proposition MinimalSuffice : forall (R A:Class) (a:U),
  A a -> (forall x, A x -> ~ R :(x,a):) -> Minimal R A a.
Proof.
  intros R A a H1 H2. split. 1: assumption.
  apply InitSegmentWhenEmpty. assumption.
Qed.

Proposition MinimalIn : forall (R A:Class) (a:U),
  Minimal R A a -> A a.
Proof.
  intros R A a [H1 _]. assumption.
Qed.

Proposition MinimalInitSegment : forall (R A:Class) (a:U),
  Minimal R A a -> initSegment R A a :~: :0:.
Proof.
  intros R A a [_ H1]. assumption.
Qed.

Proposition MinimalHasNoLesser : forall (R A:Class) (a x:U),
  A x -> Minimal R A a -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2. apply (InitSegmentWhenEmpty1 R A). 1: assumption.
  apply MinimalInitSegment. assumption.
Qed.

Proposition MinimalIsomImage : forall (F R S A B C:Class) (a:U),
  Isom F R S A B          ->
  C :<=: A                ->
  A a                     ->
  Minimal R C a           ->
  Minimal S F:[C]: (F!a).
Proof.
  intros F R S A B C a H1 H2 H3 [H4 H5]. split.
  - exists a. split. 1: assumption. apply Bij.EvalSatisfies with A B.
    2: assumption. apply Isom.IsBij with R S. assumption.
  - apply InitSegmentIsomWhenEmpty with R A B; assumption.
Qed.

