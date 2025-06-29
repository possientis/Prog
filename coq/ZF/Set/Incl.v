Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.

Export ZF.Notation.Leq.

(* Inclusion predicate between two sets.                                        *)
Definition Incl (a b:U) : Prop := Class.Incl.Incl (toClass a) (toClass b).

(* Notation "a :<=: b" := (Incl a b)                                            *)
Global Instance SetLeq : Leq U := { leq := Incl }.

(* Two sets are equal if and only if they are subsets of each other.            *)
Proposition DoubleInclusion : forall (a b:U),
  a = b <-> a :<=: b /\ b :<=: a.
Proof.
  intros a b. unfold Incl. split.
  - intros H1. split; intros x Hx.
    + rewrite <- H1. apply Hx.
    + rewrite H1. apply Hx.
  - intros [H1 H2]. apply Extensionality. intros x. split.
    + apply H1.
    + apply H2.
Qed.

(* The inclusion relation is reflexive.                                         *)
Proposition Refl : forall (a:U), a :<=: a.
Proof.
  intros a x. auto.
Qed.

(* The inclusion relation is anti-symmetric.                                    *)
Proposition Anti : forall (a b:U),
  a :<=: b -> b :<=: a -> a = b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; assumption.
Qed.

(* The inclusion relation is transitive.                                        *)
Proposition Tran : forall (a b c:U),
  a :<=: b -> b :<=: c -> a :<=: c.
Proof.
  intros a b c H1 H2 x H3. apply H2, H1, H3.
Qed.
