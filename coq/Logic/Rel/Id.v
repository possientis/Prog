Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Composition.

(* Identity operator.                                                           *)
Inductive id (a:Type) : R a a :=
| refl : forall (x:a), id a x x
.

Arguments id {a}.

Lemma id_charac : forall (a:Type) (x y:a),
    id x y <-> x = y.
Proof.
    intros a x y. split; intros H1.
    - destruct H1. reflexivity.
    - rewrite H1. constructor.
Qed.

(* left-identity law.                                                          *)
Lemma id_left : forall (a b:Type) (r:R a b), id ; r = r.
Proof.
    intros a b r. apply Ext. intros x y. unfold comp. split.
    - intros [z [H1 H2]]. destruct H2 as [y]. assumption.
    - intros H1. exists y. split.
        + assumption.
        + constructor.
Qed.

(* right-identity law.                                                           *)
Lemma id_right : forall (a b:Type) (r:R a b), r ; id = r.
Proof.
    intros a b r. apply Ext. intros x y. unfold comp. split.
    - intros [z [H1 H2]]. destruct H1. assumption.
    - intros H1. exists x. split.
        + constructor.
        + assumption.
Qed.


