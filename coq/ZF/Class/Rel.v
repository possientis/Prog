Require Import ZF.Class.
Require Import ZF.Class.Union.
Require Import ZF.Core.Or.
Require Import ZF.Set.OrdPair.

(* A class is a relation, iff its 'elements' are ordered pairs.                 *)
Definition Rel (P:Class) : Prop :=
    forall x, P x -> exists y, exists z, x = :(y,z):.

(* The union of two relation class is a relation class.                         *)
Proposition UnionRelIsRel : forall (P Q:Class),
  Rel P -> Rel Q -> Rel (P:\/:Q).
Proof.
  intros P Q Hp Hq x H1. destruct H1 as [H1|H1].
  - apply Hp, H1.
  - apply Hq, H1.
Qed.
