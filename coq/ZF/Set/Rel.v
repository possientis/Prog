Require Import ZF.Class.
Require Import ZF.Class.Rel.
Require Import ZF.Class.Union.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

Definition Rel (a:U) : Prop := Class.Rel.Rel (toClass a).

(* A relation is a set of ordered pairs.                                        *)
Proposition RelCharac : forall (a:U),
  Rel a <-> forall x, x :< a -> exists y z, x = :(y,z):.
Proof.
  intro a. unfold Rel, Class.Rel.Rel. split; auto.
Qed.

(* The union of a class of relations is a relation class.                       *)
Proposition UnionClassOfRelsIsRel : forall (P:Class),
  (forall x, P x -> Rel x) -> Class.Rel.Rel :U(P).
Proof.
  intros P H1 x H2. unfold union in H2. destruct H2 as [y [H2 H3]].
  apply H1 in H3. apply H3, H2.
Qed.
