Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Properties.
Require Import Logic.Rel.Composition.


Definition incl (a b:Type) (r s:R a b) : Prop := r = (r /\ s).
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

(* Will work for any partial order.                                             *)
Lemma eq_charac : forall (a b:Type) (r s:R a b),
    (forall (t:R a b), t <= r <-> t <= s) -> r = s.
Proof.
    intros a b r s H1. apply incl_anti.
    - apply (H1 r), incl_refl.
    - apply (H1 s), incl_refl.
Qed.

Lemma incl_inter_l : forall (a b:Type) (r s:R a b), (r /\ s) <= r.
Proof.
    intros a b r s. unfold inter. apply incl_charac. intros x y.
    intros [H1 H2]. assumption.
Qed.

Lemma incl_inter_r : forall (a b:Type) (r s:R a b), (r /\ s) <= s.
Proof.
    intros a b r s. unfold inter. apply incl_charac. intros x y.
    intros [H1 H2]. assumption.
Qed.

Lemma incl_reflexive : forall (a:Type) (r:Rel a), 
    reflexive r <-> id <= r.
Proof.
    intros a r. unfold reflexive. split; intros H1.
    - apply incl_charac. intros x y H2. destruct H2. apply H1.
    - intros x. apply incl_charac_to with id; try assumption. constructor.
Qed.

Lemma incl_symmetric : forall (a:Type) (r:Rel a),
    symmetric r <-> r <= conv r.
Proof.
    intros a r. unfold symmetric, conv. split; intros H1.
    - apply incl_charac. assumption.
    - intros x y H2. apply (incl_charac_to a a r (conv r) x y); assumption.
Qed.

Lemma incl_transitive : forall (a:Type) (r:Rel a),
    transitive r <-> r ; r <= r.
Proof.
    intros a r. unfold transitive. split; intros H1.
    - apply incl_charac. intros x y. intros [z [H2 H3]]. 
      apply H1 with z; assumption.
    - intros x z y H2 H3. apply incl_charac_to with (r;r); try assumption.
      exists z. split; assumption.
Qed.

Lemma incl_antisymmetric : forall (a:Type) (r:Rel a),
    antisymmetric r <-> (r /\ conv r) <= id.
Proof.
    intros a r. unfold antisymmetric, inter. split; intros H1.
    - apply incl_charac. intros x y [H2 H3]. rewrite (H1 x y);
      try assumption. constructor.
    - intros x y H2 H3. assert (id x y) as H4.
        { apply incl_charac_to with (r /\ conv r).
            { assumption. }
            { split; assumption. }}
      destruct H4. reflexivity.
Qed.
