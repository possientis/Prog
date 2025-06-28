Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Union2.

(* A relation is a set of ordered pairs.                                        *)
Definition Relation (f:U) : Prop :=
  forall x, x :< f -> exists y, exists z, x = :(y,z):.

(* A set if a relation iff its associated class is a relation class.            *)
Proposition ToClass : forall (f:U),
  Relation f <-> Class.Relation.Relation.Relation (toClass f).
Proof.
  intros f. split; intros H1 x H2; specialize (H1 x H2); assumption.
Qed.

(* The union of two relations is a relation.                                    *)
Proposition Union2 : forall (f g:U),
  Relation f -> Relation g -> Relation (f :\/: g).
Proof.
  intros f g H1 H2 x H3. apply Union2.Charac in H3. destruct H3 as [H3|H3].
  - apply H1, H3.
  - apply H2, H3.
Qed.

(* The union of a class of relations is a relation class.                       *)
Proposition UnionClassOfRelsIsRel : forall (A:Class),
  (forall x, A x -> Relation x) -> Class.Relation.Relation.Relation :U(A).
Proof.
  intros A H1 x H2. destruct H2 as [u [H2 H3]]. specialize (H1 u).
  apply H1 in H3. specialize (H3 x). apply H3 in H2. assumption.
Qed.

(* A relation is a subset of the product of its domain and image thereof.      *)
Proposition IsIncl : forall (f:U),
  Relation f -> f :<=: (domain f) :x: f:[domain f]:.
Proof.
  intros f H1 x H3. specialize (H1 x H3). destruct H1 as [y [z H1]].
  apply Prod.Charac. exists y. exists z. split. 1: assumption.  subst. split.
  - apply Domain.Charac. exists z. assumption.
  - apply Image.Charac. exists y. split. 2: assumption.
    apply Domain.Charac. exists z. assumption.
Qed.

