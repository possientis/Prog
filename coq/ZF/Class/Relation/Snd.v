Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Snd is the class of ordered pairs of the form ((y,z),z).                     *)
Definition Snd : Class := fun x =>
  exists y, exists z, x = :(:(y,z):,z):.

Proposition Charac2 : forall (x x':U),
  Snd :(x,x'): <-> exists y, exists z, x = :(y,z): /\ x' = z.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros x x'. split; intros H1.
  - (* If a pair is in Snd, unpack the ordered-pair equality.                   *)
    unfold Snd in H1. destruct H1 as [y [z H1]]. apply OrdPair.Equal in H1.
    exists y. exists z. assumption.
  - (* Conversely, rebuild the defining ordered pair of Snd.                    *)
    destruct H1 as [y [z [H1 H2]]]. unfold Snd. exists y. exists z.
    rewrite H1, H2. reflexivity.
Qed.

(* The class Snd is functional.                                                 *)
Proposition IsFunctional : Functional Snd.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros x x1 x2 H1 H2.
  (* Two Snd-values of the same ordered pair are both its second coordinate.    *)
  apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [y1 [z1 [H1 G1]]]. destruct H2 as [y2 [z2 [H2 G2]]].
  subst. apply OrdPair.Equal in H2. destruct H2 as [H1 H2]. subst. reflexivity.
Qed.
