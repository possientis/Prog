Require Import ZF.Class.
Require Import ZF.Class.Include.
Require Import ZF.Class.Product.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Lt.
Require Import ZF.Core.Product.
Require Import ZF.Core.Zero.
Require Import ZF.Set.Utils.

(* The class satisfied by all sets.                                             *)
Definition V : Class := fun _ => True.

(* The product of two classes is a subclass of V^2.                             *)
Proposition ProdInclV2 : forall (P Q:Class),
  P :x: Q :<=: V :x: V.
Proof.
  intros P Q x H1. destruct H1 as [y [z [H1 [H2 H3]]]].
  exists y. exists z. split.
  - apply H1.
  - split; apply I.
Qed.

(* V^2 is a strict subclass of V.                                               *)
Proposition V2InclStrictV : V :x: V :<: V.
Proof.
  apply InclStrictExists. split.
  - intros x H1. apply I.
  - exists :0:. split.
    + apply I.
    + intros [x [y [H1 _]]]. apply (EmptyNotOrdPair x y), H1.
Qed.


