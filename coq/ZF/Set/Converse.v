Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Small.
Require Import ZF.Class.Switch.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Replace2.

(* The converse of the class associated with a set is a small class.            *)
Proposition ConverseSmall : forall (a:U),
  Small (Class.Converse.converse (toClass a)).
Proof.
  (* Let a be an arbitary set. *)
  intros a.

  (* We have the class equivalence Switch[a] ~ converse a. *)
  apply SmallEquivCompat with Switch:[toClass a]:. 1: apply ImageBySwitch.

  (* So it is sufficient to prove that Switch[a] is small. *)
  assert (Small (Switch:[toClass a]:)) as A. 2: apply A.

  (* This follows from the fact that Switch is functional and a is small. *)
  apply ReplaceSmall.

  - apply SwitchIsFunctional.

  - apply SetIsSmall.
Qed.

(* The converse of a set.                                                       *)
Definition converse (a:U) : U
  := fromClass (Class.Converse.converse (toClass a)) (ConverseSmall a).

Proposition ConverseCharac : forall (a:U),
  forall x, x :< (converse a) <-> exists y z, x =:(z,y): /\ :(y,z): :< a.
Proof.
  intros a x. unfold converse. split; intros H1.
  - apply FromClassCharac, Class.Converse.ConverseCharac in H1. apply H1.
  - apply FromClassCharac, Class.Converse.ConverseCharac, H1.
Qed.
