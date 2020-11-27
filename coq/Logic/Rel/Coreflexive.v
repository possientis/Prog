Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Properties.
Require Import Logic.Rel.Composition.

Definition coreflexive (a:Type) (r:Rel a) : Prop := r <= id.

Arguments coreflexive {a}.

Lemma corefl_sym : forall (a:Type) (r:Rel a), coreflexive r -> symmetric r.
Proof.
    unfold coreflexive, symmetric. intros a r H1 x y H2. 
    generalize H2. intros H3.
    apply (incl_charac_to a a r id) in H2; try assumption. 
    destruct H2. assumption.
Qed.

Lemma corefl_trans : forall (a:Type) (r:Rel a), coreflexive r -> transitive r.
Proof.
    unfold coreflexive, transitive. intros a r H1 x y z H2 H3.
    generalize H2. intros H4.
    apply (incl_charac_to a a r id) in H2; try assumption. 
    apply (incl_charac_to a a r id) in H3; try assumption. 
    destruct H2. destruct H3. assumption.
Qed.

Lemma corefl_id : forall (a:Type) (r:Rel a),
    coreflexive r -> id <= r <-> id = r.
Proof.
    intros a r H1. split; intros H2.
    - apply incl_anti; assumption.
    - rewrite H2. apply incl_refl.
Qed.

Lemma corefl_comp : forall (a:Type) (r s:Rel a), 
    coreflexive r -> 
    coreflexive s ->
    s ; r = (s /\ r).
Proof.
    intros a r s H1 H2. apply Ext. intros x y. split; intros H3.
    - destruct H3 as [z [H3 H4]]. 
      apply (incl_charac_to _ _ r id x z) in H1; try assumption.
      apply (incl_charac_to _ _ s id z y) in H2; try assumption.
      destruct H1, H2. split; assumption.
    - destruct H3 as [H3 H4].
      apply (incl_charac_to _ _ r id x y) in H1; try assumption.
      destruct H1. exists x. split; assumption.
Qed.

Lemma corefl_ex4_11_1 : forall (a:Type) (r s:Rel a),
    coreflexive s -> 
    ((s ; r) /\ id) = ((r ; s) /\ id).
Proof.
    intros a r s H1. apply Ext. intros x y. split; intros H2.
    - destruct H2 as [[z [H2 H3]] H4]. destruct H4. split; try constructor.
      apply (incl_charac_to _ _ s id z x) in H1; try assumption.
      destruct H1. exists x. split; assumption.
    - destruct H2 as [[z [H2 H3]] H4]. destruct H4. split; try constructor.
      apply (incl_charac_to _ _ s id x z) in H1; try assumption.
      destruct H1. exists x. split; assumption.
Qed.

Lemma corefl_ex4_11_2 : forall (a:Type) (r s:Rel a),
    coreflexive s -> 
    ((s ; r) /\ id) = ((s ; r ; s) /\ id).
Proof.
    intros a r s H1. apply Ext. intros x y. split; intros H2.
    - destruct H2 as [[z [H2 H3]] H4]. destruct H4. split; try constructor.
      apply (incl_charac_to _ _ s id z x) in H1; try assumption.
      destruct H1. exists x. split; try assumption. exists x. split; assumption. 
    - destruct H2 as [[z [[u [H2 H3]] H4]] H5]. destruct H5. 
      split; try constructor.
      apply (incl_charac_to _ _ s id x u) in H1; try assumption. destruct H1.
      exists z. split; assumption.
Qed.
