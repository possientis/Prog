Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Lt.
Require Import ZF.Set.

(* Inclusion predicate between two classes.                                     *)
Definition Incl (P Q:Class) : Prop := forall x, P x -> Q x.

(* Notation "P :<=: Q" := (Incl P Q)                                            *)
Global Instance ClassLeq : Leq Class := { leq := Incl }.

(* Strict inclusion predicate.                                                  *)
Definition InclStrict (P Q:Class) : Prop := P :<=: Q /\ ~P :~: Q.

(* Notation "P :<: Q" := (InclStrict P Q)                                       *)
Global Instance ClassLt : Lt Class := { lt := InclStrict }.

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

(* The inclusion relation is reflexive.                                         *)
Proposition InclRefl : forall (P:Class), P :<=: P.
Proof.
  intros P x. auto.
Qed.

(* The inclusion relation is 'anti-symmetric' (modulo equivalence).             *)
Proposition InclAnti : forall (P Q:Class),
  P :<=: Q -> Q :<=: P -> P :~: Q.
Proof.
  intros P Q H1 H2. apply DoubleInclusion. split; assumption.
Qed.

(* The inclusion relation is transitive.                                        *)
Proposition InclTran : forall (P Q R:Class),
  P :<=: Q -> Q :<=: R -> P :<=: R.
Proof.
  intros P Q R H1 H2 x H3. apply H2, H1, H3.
Qed.

(* A more convenient characterisation of strict inclusion between classes.      *)
Proposition InclStrictExists : forall (P Q:Class),
  P :<: Q <-> P :<=: Q /\ exists x, Q x /\ ~ P x.
Proof.
  intros P Q. split; intros H1.
  - unfold InclStrict in H1. destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply NotForAllNot. intros H3. apply H2. apply DoubleInclusion. split.
      * apply H1.
      * intros x H4. apply DoubleNegation. intros H5. apply (H3 x). split; assumption.
  - destruct H1 as [H1 [x [H2 H3]]]. unfold InclStrict. split.
    + apply H1.
    + intros H4. apply H3, H4, H2.
Qed.
