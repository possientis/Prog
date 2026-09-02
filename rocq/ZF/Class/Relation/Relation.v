Require Import ZF.Class.Equiv.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

(* A relation class is a class whose elements are ordered pairs.                *)
Definition Relation (F:Class) : Prop :=
    forall x, F x -> exists y, exists z, x = :(y,z):.

(* The relation property is compatible with class equivalence.                  *)
Proposition EquivCompat : forall (F G:Class),
  F :~: G -> Relation F -> Relation G.
Proof.
  intros F G H1 H2 x H3. apply H1 in H3. specialize (H2 x H3). assumption.
Qed.

(* The union of two relations classes is a relation class.                      *)
Proposition Union2 : forall (F G:Class),
  Relation F -> Relation G -> Relation (F:\/:G).
Proof.
  intros F G H1 H2 x [H3|H3].
  - apply H1, H3.
  - apply H2, H3.
Qed.

(* A functional relation with a small domain is small.                          *)
Proposition IsSmall : forall (F:Class),
  Relation F -> Functional F -> Small (domain F) -> Small F.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros F H1 H2 H3. apply Bounded.IsSmall.
  destruct H3 as [a H3].
  assert (Small F:[domain F]:) as H4. {
    apply Image.IsSmallR. 1: assumption. exists a. assumption. }
  destruct H4 as [b H4].
  exists :P(:P(a:\/:b)). intros x H5. specialize (H1 x H5).
  destruct H1 as [y [z H1]]. subst. apply Power.Charac. intros u H6.
  apply OrdPair.Charac in H6. destruct H6 as [H6|H6]; rewrite H6.
  - apply Power.Charac. intros v H7. apply Single.Charac in H7.
    subst. apply Union2.Charac. left. apply H3. exists z. assumption.
  - apply Power.Charac. intros v H7. apply Pair.Charac in H7.
    apply Union2.Charac. destruct H7 as [H7|H7]; subst.
    + left. apply H3. exists z. assumption.
    + right. apply H4. exists y. split. 2: assumption.
      exists z. assumption.
Qed.

