Require Import ZF.Class.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Union.
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

(* The union of a class of relations is a relation class.                       *)
Proposition UnionClassOfRelsIsRel : forall (P:Class),
  (forall x, P x -> Relation x) -> Class.Relation.Relation :U(P).
Proof.
  intros P H1 x H2. unfold unionClass in H2. destruct H2 as [y [H2 H3]].
  apply H1 in H3. apply H3, H2.
Qed.
