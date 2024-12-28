Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Lt.
Require Import ZF.Set.

(* Inclusion predicate between two sets.                                        *)
Definition Incl (a b:U) : Prop := Class.Incl.Incl (toClass a) (toClass b).

(* Notation "a :<=: b" := (Incl a b)                                            *)
Global Instance SetLeq : Leq U := { leq := Incl }.

(* Strict inclusion predicate.                                                  *)
Definition InclStrict (a b:U) : Prop := a :<=: b /\ ~a = b.

(* Notation "a :<: b" := (InclStrict a b)                                       *)
Global Instance SetLt : Lt U := { lt := InclStrict }.

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
Proposition InclRefl : forall (a:U), a :<=: a.
Proof.
  intros a x. auto.
Qed.

(* The inclusion relation is anti-symmetric.                                    *)
Proposition InclAnti : forall (a b:U),
  a :<=: b -> b :<=: a -> a = b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; assumption.
Qed.

(* The inclusion relation is transitive.                                        *)
Proposition InclTran : forall (a b c:U),
  a :<=: b -> b :<=: c -> a :<=: c.
Proof.
  intros a b c H1 H2 x H3. apply H2, H1, H3.
Qed.

Proposition InclStrictExists : forall (a b:U),
  a :<: b <-> a :<=: b /\ exists x, x :< b /\ ~ x :< a.
Proof.
  intros a b. split; intros H1.
  - unfold InclStrict in H1. destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply NotForAllNot. intros H3. apply H2. apply DoubleInclusion. split.
      * apply H1.
      * intros x H4. apply DoubleNegation. intros H5. apply (H3 x). split; assumption.
  - destruct H1 as [H1 [x [H2 H3]]]. unfold InclStrict. split.
    + apply H1.
    + intros H4. subst. contradiction.
Qed.
