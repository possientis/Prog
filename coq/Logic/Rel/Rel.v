Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Func.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Composition.

Inductive Void : Type :=.

Notation "0" := (Void) : Rel_scope.

Open Scope Rel_scope.

Definition initial (a:Type) : R 0 a := fun x y => False.

Arguments initial {a}.

Definition terminal (a:Type) : R a 0 := fun x y => False.

Arguments terminal {a}.

Lemma initial_existence : forall (a:Type), exists (r:R 0 a), True.
Proof.
    intros a. exists initial. trivial.
Qed.

Lemma initial_uniqueness : forall (a:Type) (r s:R 0 a), r = s.
Proof.
    intros a r s. apply Ext. intros x y. split; intros H1; inversion x.
Qed.

Lemma terminal_existence : forall (a:Type), exists (r:R a 0), True.
Proof.
    intros a. exists terminal. trivial.
Qed.

Lemma terminal_uniqueness : forall (a:Type) (r s:R a 0), r = s.
Proof.
    intros a r s. apply Ext. intros x y. split; intros H1; inversion y.
Qed.

