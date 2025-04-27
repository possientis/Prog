Require Import ZF.Axiom.Extensionality.
Require Import ZF.Set.Core.

Require Import ZF.Notation.Equiv.
Export ZF.Notation.Equiv.

(* A class is simply a predicate on sets.                                       *)
Definition Class : Type := U -> Prop.

(* A set can be viewed as a class.                                              *)
Definition toClass (a:U) : Class := fun x => x :< a.

(* Natural equivalence between classes.                                         *)
Definition classEquiv (P Q:Class) : Prop := forall x, P x <-> Q x.

(* Notation "P :~: Q" := (classEquiv P Q)                                       *)
Global Instance Equiv : Equiv Class := { equiv := classEquiv }.

(* The equivalence between classes is reflexive.                                *)
Proposition EquivRefl : forall (P:Class), P :~: P.
Proof.
  intros P x. split; intros H1; apply H1.
Qed.

(* The equivalence between classes is symmetric.                                *)
Proposition EquivSym : forall (P Q:Class), P :~: Q ->  Q :~: P.
Proof.
  intros P Q. intros H1 x. split; intros H2; apply H1, H2.
Qed.

(* The equivalence between classes is transitive.                               *)
Proposition EquivTran : forall (P Q R:Class),
  P :~: Q -> Q :~: R -> P :~: R.
Proof.
  intros P Q R. intros H1 H2 x. split; intros H3.
  - apply H2, H1, H3.
  - apply H1, H2, H3.
Qed.

Proposition NotEquivSym : forall (P Q:Class), P :<>: Q -> Q :<>: P.
Proof.
  intros P Q H1 H2. apply H1, EquivSym. assumption.
Qed.

Proposition EquivSetEqual : forall (a b:U),
  toClass a :~: toClass b <-> a = b.
Proof.
  intros a b. split.
  - apply Extensionality.
  - intros H1. subst. apply EquivRefl.
Qed.

Proposition NotEquivSetNotEqual : forall (a b:U),
  toClass a :<>: toClass b <-> a <> b.
Proof.
  intros a b. split; intros H1 H2; apply H1, EquivSetEqual; assumption.
Qed.

Proposition NotEquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :<>: R -> Q :<>: S.
Proof.
  intros P Q R S H1 H2 H3 H4. apply H3.
  apply EquivTran with Q. 1: assumption.
  apply EquivTran with S. 1: assumption.
  apply EquivSym. assumption.
Qed.

Proposition NotEquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :<>: R -> Q :<>: R.
Proof.
  intros P Q R H1. apply NotEquivCompat.
  - assumption.
  - apply EquivRefl.
Qed.

Proposition NotEquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :<>: P -> R :<>: Q.
Proof.
  intros P Q R H1. apply NotEquivCompat.
  - apply EquivRefl.
  - assumption.
Qed.

