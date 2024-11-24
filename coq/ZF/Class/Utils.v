Require Import ZF.Axiom.Core.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Class.
Require Import ZF.Class.Include.
Require Import ZF.Class.Intersect.
Require Import ZF.Class.Product.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Class.V.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.
Require Import ZF.Set.Utils.

Definition CRelation := ZF.Class.Relation.Relation.
Definition SRelation := ZF.Set.Relation.Relation.

Proposition SmallIntersectSmall1 : forall (P Q:Class),
  Small P -> Small P:/\:Q.
Proof.
  intros P Q [a Ha].
  apply BoundedClassIsSmall. exists a.
  intros x [H1 _]. apply Ha, H1.
Qed.

Proposition SmallIntersectSmall2 : forall (P Q:Class),
  Small Q -> Small P:/\:Q.
Proof.
  intros P Q [a Ha]. apply BoundedClassIsSmall. exists a.
  intros x [_ H1]. apply Ha, H1.
Qed.
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

(* The union of two relation class is a relation class.                         *)
Proposition UnionRelIsRel : forall (P Q:Class),
  CRelation P -> CRelation Q -> CRelation P:\/:Q.
Proof.
  intros P Q Hp Hq x H1. destruct H1 as [H1|H1].
  - apply Hp, H1.
  - apply Hq, H1.
Qed.

(* The union of a class of relations is a relation class.                       *)
Proposition UnionClassOfRelsIsRel : forall (P:Class),
  (forall x, P x -> SRelation x) -> CRelation :U(P).
Proof.
  intros P H1 x H2. unfold unionClass in H2. destruct H2 as [y [H2 H3]].
  apply H1 in H3. apply H3, H2.
Qed.

(* When two ordered pairs belong to a one-to-one class, equality between the    *)
(* first coordinates is equivalent to equality between the second coordinates.  *)
Proposition OneToOneCoordEquiv : forall (P:Class) (x1 x2 y1 y2:U),
  OneToOne P -> P :(x1,y1): -> P :(x2,y2): -> x1 = x2 <-> y1 = y2.
Proof.
  intros P x1 x2 y1 y2 H3 H1 H2. split; intros H4.
  - subst. apply OneToOneCharac1 with P x2; assumption.
  - subst. apply OneToOneCharac2 with P y2; assumption.
Qed.

