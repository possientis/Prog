Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.

Require Import ZF.Notation.Lt.
Export ZF.Notation.Lt.

(* Strict inclusion predicate.                                                  *)
Definition Less (P Q:Class) : Prop := P :<=: Q /\ P :<>: Q.

(* Notation "P :<: Q" := (Less P Q)                                             *)
Global Instance ClassLt : Lt Class := { lt := Less }.


Proposition EquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :<: R -> Q :<: S.
Proof.
  intros P Q R S H1 H2 [H3 H4]. split.
  - apply Incl.EquivCompat with P R; assumption.
  - intros H5. apply H4. apply EquivTran with Q. 1: assumption.
    apply EquivTran with S. 1: assumption. apply EquivSym. assumption.
Qed.

Proposition EquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :<: R -> Q :<: R.
Proof.
  intros P Q R H1. apply EquivCompat.
  - assumption.
  - apply EquivRefl.
Qed.

Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :<: P -> R :<: Q.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply EquivRefl.
  - assumption.
Qed.

(* A more convenient characterisation of strict inclusion between classes.      *)
Proposition Exists : forall (P Q:Class),
  P :<: Q <-> P :<=: Q /\ exists x, Q x /\ ~ P x.
Proof.
  intros P Q. split; intros H1.
  - destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply NotForAllNot. intros H3. apply H2. apply DoubleInclusion. split.
      * apply H1.
      * intros x H4. apply DoubleNegation. intros H5. apply (H3 x). split; assumption.
  - destruct H1 as [H1 [x [H2 H3]]]. split.
    + apply H1.
    + intros H4. apply H3, H4, H2.
Qed.

Proposition InclLessTran : forall (P Q R:Class),
  P :<=: Q -> Q :<: R -> P :<: R.
Proof.
  intros P Q R H1 [H2 H3]. split.
  - apply Incl.Tran with Q; assumption.
  - intros H4. apply H3, DoubleInclusion. split. 1: assumption.
    apply Incl.EquivCompatL with P; assumption.
Qed.

Proposition LessInclTran : forall (P Q R:Class),
  P :<: Q -> Q :<=: R -> P :<: R.
Proof.
  intros P Q R [H1 H2] H3. split.
  - apply Incl.Tran with Q; assumption.
  - intros H4. apply H2, DoubleInclusion. split. 1: assumption.
    apply Incl.EquivCompatR with R. 2: assumption. apply EquivSym. assumption.
Qed.

Proposition EquivOrLess : forall (P Q:Class),
  P :<=: Q <-> P :~: Q \/ P :<: Q.
Proof.
  intros P Q. split; intros H1.
  - assert (P :~: Q \/ P :<>: Q) as H2. { apply LawExcludedMiddle. }
    destruct H2 as [H2|H2].
    + left. assumption.
    + right. split; assumption.
  - destruct H1 as [H1|H1].
    + apply Incl.EquivCompatR with P. 1: assumption. apply Incl.Refl.
    + apply H1.
Qed.
