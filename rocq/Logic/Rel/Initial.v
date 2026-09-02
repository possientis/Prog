Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.

Declare Scope Rel_Initial_scope.

(* The category of relations has an initial object namely 0.                    *)

Inductive Void : Prop :=.

Notation "0" := (Void) : Rel_Initial_scope.

Open Scope Rel_Initial_scope.

(* Arrow needed for initial object universal property.                          *)
Definition initial (a:Type) : R 0 a := fun x y => False.

Arguments initial {a}.

(* Existence part of universal property                                         *)
Lemma initial_existence : forall (a:Type), exists (r:R 0 a), True.
Proof.
    intros a. exists initial. trivial.
Qed.

(* Uniqueness part of universal property                                        *)
Lemma initial_uniqueness : forall (a:Type) (r s:R 0 a), r = s.
Proof.
    intros a r s. apply Ext. intros x y. split; intros H1; inversion x.
Qed.
