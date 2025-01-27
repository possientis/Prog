Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Image.
Require Import ZF.Class.InvImage.
Require Import ZF.Core.Image.
Require Import ZF.Core.Inverse.
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
