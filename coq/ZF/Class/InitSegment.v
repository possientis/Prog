Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Image.
Require Import ZF.Class.Inter.
Require Import ZF.Class.InvImage.
Require Import ZF.Core.And.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Core.Inverse.
Require Import ZF.Core.Zero.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Singleton.

(* The inital segment is the inverse image of the singleton {a}.                *)
Definition initSegment (R:Class) (a:U) : Class := R^:-1: :[ toClass :{a}: ]:.

Proposition InitSegmentCharac : forall (R:Class) (a x:U),
  initSegment R a x <-> R :(x,a):.
Proof.
  intros R a x. split; intros H1.
  - apply InvImageCharac in H1. destruct H1 as [y [H1 H2]].
    apply SingleCharac in H1. subst. assumption.
  - apply InvImageCharac. exists a. split. 2: assumption. apply SingleIn.
Qed.

Proposition InitSegmentEmptyInter : forall (R A:Class) (a:U),
  A :/\: initSegment R a :~: :0: <-> forall x, A x -> ~ R :(x,a):.
Proof.
  intros R A a. split; intros H1.
  - intros x H2 H3. apply EmptyCharac with x. apply H1, InterCharac.
    split. 1: assumption. apply InitSegmentCharac. assumption.
  - intros x. split; intros H2.
    + apply EmptyCharac.
      apply (proj1 (InterCharac _ _ _)) in H2. destruct H2 as [H2 H3].
      apply InitSegmentCharac in H3. apply (H1 x); assumption.
    + apply EmptyCharac in H2. contradiction.
Qed.

Proposition InitSegmentEmptyInter1 : forall (R A:Class) (a x:U),
  A :/\: initSegment R a :~: :0: -> A x -> ~ R :(x,a):.
Proof.
  intros R A a x H1 H2. apply (proj1 (InitSegmentEmptyInter R A a)); assumption.
Qed.

