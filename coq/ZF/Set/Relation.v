Require Import ZF.Class.
Require Import ZF.Class.Relation.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* A relation is a set of ordered pairs.                                        *)
Definition Relation (a:U) : Prop
  := Class.Relation.Relation (toClass a).

Proposition RelationCharac : forall (a:U),
  Relation a <-> forall x, x :< a -> exists y z, x = :(y,z):.
Proof.
  intro a. unfold Relation, Class.Relation.Relation. split; auto.
Qed.
