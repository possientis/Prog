Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.Initial.
Require Import Logic.Rel.R.

(* The category of relations has a terminal object namely 0.                     *)

(* Arrow needed for terminal object universal property.                          *)
Definition terminal (a:Type) : R a 0 := fun x y => False.

Arguments terminal {a}.

(* Existence part of universal property                                         *)
Lemma terminal_existence : forall (a:Type), exists (r:R a 0), True.
Proof.
    intros a. exists terminal. trivial.
Qed.

(* Uniqueness part of universal property                                        *)
Lemma terminal_uniqueness : forall (a:Type) (r s:R a 0), r = s.
Proof.
    intros a r s. apply Ext. intros x y. split; intros H1; inversion y.
Qed.

