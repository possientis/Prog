
Require Import ZF.Axiom.Core.
Require Import ZF.Class.Class.
Require Import ZF.Class.Include.
Require Import ZF.Class.Product.
Require Import ZF.Class.Relation.
Require Import ZF.Class.V.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Utils.

(* The converse of the converse is a subclass of the original class.            *)
Proposition ConverseConverseIncl : forall (P:Class),
  converse (converse P) :<=: P.
Proof.
  intros P x H1. apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]].
  apply ConverseCharac in H2. destruct H2 as [z' [y' [H2 H3]]].
  apply OrdPairEqual in H2. destruct H2 as [H2 H2']. subst. apply H3.
Qed.

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

