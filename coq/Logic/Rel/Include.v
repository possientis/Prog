Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Intersect.

Definition incl (a b:Type) (r s:R a b) : Prop := r = inter r s.
Arguments incl {a} {b}.

Notation "r <= s" := (incl r s)
    (at level 70, no associativity) : Rel_Include_scope.

Open Scope Rel_Include_scope.

Lemma incl_charac : forall (a b:Type) (r s:R a b),
    r <= s <-> forall (x:a) (y:b), r x y -> s x y.
Proof.
    intros a b r s. unfold incl, inter. split; intros H1.
    - intros x y H2. rewrite H1 in H2. destruct H2 as [H2 H3]. assumption.
    - apply Ext. intros x y. split; intros H2.
        + split; try assumption. apply H1. assumption.
        + destruct H2 as [H2 H3]. assumption.
Qed.

Lemma incl_charac_to : forall (a b:Type) (r s:R a b) (x:a) (y:b),
    r <= s -> r x y -> s x y.
Proof.
    intros a b r s x y H1. revert x y. apply incl_charac. assumption.
Qed.


Lemma incl_refl : forall (a b:Type) (r:R a b), r <= r.
Proof.
    intros a b r. apply incl_charac. intros x y. auto.
Qed.


Lemma incl_anti : forall (a b:Type) (r s:R a b), 
    r <= s -> s <= r -> r = s.
Proof.
    intros a b r s H1 H2. apply Ext. intros x y. split; intros H3.
    - apply incl_charac_to with r; assumption.
    - apply incl_charac_to with s; assumption.
Qed.

Lemma incl_trans : forall (a b:Type) (r s t:R a b),
    r <= s -> s <= t -> r <= t.
Proof.
    intros a b r s t H1 H2. apply incl_charac. intros x y H3.
    apply incl_charac_to with s; try assumption.
    apply incl_charac_to with r; try assumption.
Qed.
