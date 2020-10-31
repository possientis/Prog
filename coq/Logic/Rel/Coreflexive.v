Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Properties.

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


