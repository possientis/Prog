Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Composition.
Require Import Logic.Rel.Coreflexive.

(* Range of a relation defined as coreflexive relation rather than set          *)
Inductive rng (a b:Type) (r:R a b) : Rel b :=
| mkDom : forall (y:b), (exists (x:a), r x y) -> rng a b r y y
.

Arguments rng {a} {b}.

Lemma rng_corefl : forall (a b:Type) (r:R a b), coreflexive (rng r).
Proof.
    unfold coreflexive. intros a b r. apply incl_charac. intros x y H1.
    destruct H1. constructor.
Qed.


Lemma rng_universal : forall (a b:Type) (r:R a b) (s:Rel b), s <= id -> 
    rng r <= s <-> r <= s ; r.
Proof.
    intros a b r s H1. split; intros H2; apply incl_charac; intros x y H3.
    - unfold comp. exists y. split; try assumption. 
      assert (rng r y y) as H4.
        { constructor. exists x. assumption. }
      apply incl_charac_to with (rng r); assumption.
    - destruct H3 as [y [x H3]]. 
      apply (incl_charac_to _ _ _ (s ; r)) in H3; try assumption.
      unfold comp in H3. destruct H3 as [z [H3 H4]]. generalize H4. intros H4'.
      apply (incl_charac_to _ _ _ id) in H4'; try assumption. 
      destruct H4'. assumption.
Qed.

Lemma rng_inter : forall (a b:Type) (r:R a b),
    rng r = ((r ; conv r) /\ id).
Proof.
    intros a b r. apply Ext. intros x y. split; intros H1.
    - destruct H1 as [y [x H1]]. unfold inter, conv, comp. split.
        + exists x. split; assumption.
        + constructor.
    - unfold inter in H1. destruct H1 as [H1 H2]. destruct H2 as [y].
      constructor. unfold comp in H1. destruct H1 as [x [H1 H2]].
      exists x. assumption.
Qed.

Lemma rng_comp_self : forall (a b:Type) (r:R a b), r = rng r ; r.
Proof.
    intros a b r. apply Ext. intros x y. unfold comp. split; intros H1.
    - exists y. split; try assumption. constructor. exists x. assumption.
    - destruct H1 as [z [H1 H2]]. destruct H2. assumption.
Qed.

Lemma rng_comp : forall (a b c:Type) (r:R a b) (s:R b c),
    rng (s ; r) = rng (s ; rng r).
Proof.
    intros a b c r s. apply Ext. intros x y. split; intros H1.
    - destruct H1 as [y [x H1]]. constructor. unfold comp in H1.
      destruct H1 as [z [H1 H2]]. exists z. unfold comp. exists z.
      split; try assumption. constructor. exists x. assumption.
    - destruct H1 as [y [x H1]]. constructor. unfold comp in H1.
      destruct H1 as [z [H1 H2]]. destruct H1 as [z [x H1]].
      exists x. exists z. split; assumption.
Qed.


