Require Import ZF.Class.Equiv.

Require Import ZF.Notation.Leq.
Export ZF.Notation.Leq.

(* Inclusion predicate between two classes.                                     *)
Definition Incl (P Q:Class) : Prop := forall x, P x -> Q x.

(* Notation "P :<=: Q" := (Incl P Q)                                            *)
Global Instance ClassLeq : Leq Class := { leq := Incl }.

(* Two classes are equivalent if and only if they are included in each other.   *)
Proposition DoubleInclusion : forall (P Q:Class),
  P :~: Q <-> P :<=: Q /\ Q :<=: P.
Proof.
  intros P Q. split; intros H1.
  - split; intros x; apply H1.
  - intros x. destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply H2.
Qed.

Proposition EquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :<=: R -> Q :<=: S.
Proof.
  intros P Q R S H1 H2 H3 x H4. apply H2, H3, H1, H4.
Qed.

Proposition EquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :<=: R -> Q :<=: R.
Proof.
  intros P Q R H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :<=: P -> R :<=: Q.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

(* The inclusion relation is reflexive.                                         *)
Proposition Refl : forall (P:Class), P :<=: P.
Proof.
  intros P x. auto.
Qed.

(* The inclusion relation is 'anti-symmetric' (modulo equivalence).             *)
Proposition Anti : forall (P Q:Class),
  P :<=: Q -> Q :<=: P -> P :~: Q.
Proof.
  intros P Q H1 H2. apply DoubleInclusion. split; assumption.
Qed.

(* The inclusion relation is transitive.                                        *)
Proposition Tran : forall (P Q R:Class),
  P :<=: Q -> Q :<=: R -> P :<=: R.
Proof.
  intros P Q R H1 H2 x H3. apply H2, H1, H3.
Qed.
