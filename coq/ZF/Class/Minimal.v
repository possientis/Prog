Require Import ZF.Class.
Require Import ZF.Class.Empty.
Require Import ZF.Class.InitSegment.
Require Import ZF.Class.Inter.
Require Import ZF.Core.And.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Zero.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that a is an R-minimal element of A.           *)
Definition Minimal (R A:Class) (a:U) : Prop
  := A a /\ A :/\: initSegment R a :~: :0:.

Proposition MinimalIn : forall (R A:Class) (a:U),
  Minimal R A a -> A a.
Proof.
  intros R A a [H1 _]. assumption.
Qed.

Proposition MinimalEmptyInter : forall (R A:Class) (a:U),
  Minimal R A a -> A :/\: initSegment R a :~: :0:.
Proof.
  intros R A a [_ H2]. assumption.
Qed.

Proposition MinimalHasNoPred : forall (R A:Class) (a x:U),
  Minimal R A a -> A x -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2. apply MinimalEmptyInter in H1.
  remember (proj1 (InitSegmentEmptyInter R A a) H1) as H3 eqn:E. clear E H1.
  apply H3. assumption.
Qed.

Proposition MinimalSuffice : forall (R A:Class) (a:U),
  A a -> (forall x, A x -> ~ R :(x,a):) -> Minimal R A a.
Proof.
  intros R A a H1 H2. split. 1: assumption.
  apply InitSegmentEmptyInter. assumption.
Qed.

