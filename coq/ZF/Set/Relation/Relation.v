Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* A set is a relation iff its associated class is.                             *)
Definition Relation (a:U) : Prop := Relation (toClass a).

(* A relation is a set of ordered pairs.                                        *)
Proposition Charac : forall (a:U),
  Relation a <-> forall x, x :< a -> exists y z, x = :(y,z):.
Proof.
  intro a. split; auto.
Qed.

(* The union of a class of relations is a relation class.                       *)
Proposition UnionClassOfRelsIsRel : forall (P:Class),
  (forall x, P x -> Relation x) -> Class.Relation.Relation.Relation :U(P).
Proof.
  intros P H1 x H2. unfold union in H2. destruct H2 as [y [H2 H3]].
  apply H1 in H3. apply H3, H2.
Qed.
