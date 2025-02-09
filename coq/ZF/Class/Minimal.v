Require Import ZF.Class.
Require Import ZF.Class.Empty.
Require Import ZF.Class.InitSegment.
Require Import ZF.Class.Inter.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that a is an R-minimal element of A.           *)
Definition Minimal (R A:Class) (a:U) : Prop
  := A a /\ initSegment R A a :~: :0:.

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
