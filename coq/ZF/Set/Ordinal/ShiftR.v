Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.ShiftR.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.

Module COS := ZF.Class.Ordinal.ShiftR.

(* Shifting a function to the right. shiftR a f = {(0,a)}\/{(succ x,y)|(x,y):<f}*)
Definition shiftR (a f:U) : U := fromClass (COS.shiftR a (toClass f))
  (COS.IsSmall (toClass f) a (SetIsSmall f)).

Proposition ToClass : forall (f a:U),
  toClass (shiftR a f) :~: COS.shiftR a (toClass f).
Proof.
  intros f a. apply ToFromClass.
Qed.

Proposition Charac : forall (f a x:U),
  x :< shiftR a f <->
  x = :(:0:,a): \/ exists y z, x = :(succ y,z): /\ :(y,z): :< f.
Proof.
  intros f a x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [H1|H1].
    + left. assumption.
    + right. assumption.
  - apply FromClass.Charac. destruct H1 as [H1|H1].
    + left. assumption.
    + right. assumption.
Qed.


