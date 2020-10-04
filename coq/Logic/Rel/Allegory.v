Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Composition.

Lemma comp_semi_distrib_inter_l : forall (a b c:Type) (r s:R a b) (t:R b c), 
    t ; (r /\ s) <= ((t ; r) /\ (t ; s)).
Proof.
    intros a b c r s t. apply incl_charac. intros x y.
    unfold comp, inter. intros [z [[H1 H2] H3]]. 
    split; exists z; split; assumption.
Qed.

Lemma comp_semi_distrib_inter_r : forall (a b c:Type) (t:R a b) (r s:R b c),
    (r /\ s) ; t <= ((r ; t) /\ (s ; t)).
Proof.
    intros a b c t r s. apply incl_charac. intros x y.
    unfold comp, inter. intros [z [H1 [H2 H3]]]. 
    split; exists z; split; assumption.
Qed.

(* Intuition: factor out rhs of composition.                                    *)
Lemma modulatity_law_r : forall (a b c:Type) (r:R a b) (s:R b c) (t:R a c),
    ((s ; r) /\ t) <= (s /\ (t ; conv r)) ; r.  
Proof.
    intros a b c r s t. apply incl_charac. intros x y.
    unfold comp, inter, conv. intros [[z [H1 H2]] H3]. exists z.
    split; try assumption. split; try assumption. exists x. split; assumption.
Qed.


(* Intuition: factor out lhs of composition.                                    *)
Lemma modularity_law_l : forall (a b c:Type) (r:R a b) (s:R b c) (t:R a c),
    ((s ; r) /\ t) <= s ; (r /\ (conv s ; t)).  
Proof.
    intros a b c r s t. apply incl_charac. intros x y.
    unfold comp, inter, conv. intros [[z [H1 H2]] H3]. exists z.
    split; try assumption. split; try assumption. exists y. split; assumption.
Qed.

(* Intuition: factorize composition.                                            *)
Lemma modularity_law_sym : forall (a b c:Type) (r:R a b) (s:R b c) (t:R a c),
    ((s ; r) /\ t) <= (s /\ (t ; conv r)) ; (r /\ (conv s ; t)).
Proof.
    intros a b c r s t. apply incl_charac. intros x y.
    unfold comp, inter, conv. intros [[z [H1 H2]] H3]. exists z. split.
    - split; try assumption. exists y. split; assumption.
    - split; try assumption. exists x. split; assumption.
Qed.

Lemma modularity_law_id : forall (a b:Type) (r s:R a b),
    ((conv r ; s ) /\ id) <= conv (r /\ s) ; (r /\ s).
Proof.
    intros a b r s. apply incl_charac. intros x y.
    unfold comp, inter, conv. intros [[z [H1 H2]] H3]. destruct H3. exists z.
    split; split; assumption.
Qed.


Lemma comp_incl_compat_l : forall (a b c:Type) (r:R a b) (s1 s2:R b c),
    s1 <= s2 -> s1 ; r <= s2 ; r.
Proof.
    intros a b c r s1 s2 H1. apply incl_charac. intros x y. unfold comp.
    intros [z [H2 H3]]. exists z. split.
    - assumption.
    - apply incl_charac_to with s1; assumption.
Qed.

Lemma comp_incl_compat_r : forall (a b c:Type) (r1 r2:R a b) (s:R b c),
    r1 <= r2 -> s ; r1 <= s ; r2.
Proof.
    intros a b c r1 r2 s H1. apply incl_charac. intros x y. unfold comp.
    intros [z [H2 H3]]. exists z. split.
    - apply incl_charac_to with r1; assumption.
    - assumption.
Qed.

Lemma comp_incl_compat: forall (a b c:Type) (r1 r2:R a b) (s1 s2:R b c),
    r1 <= r2 -> s1 <= s2 -> s1 ; r1 <= s2 ; r2.
Proof.
    intros a b c r1 r2 s1 s2 H1 H2. apply incl_charac. intros x y. unfold comp.
    intros [z [H3 H4]]. exists z. split.
    - apply incl_charac_to with r1; assumption.
    - apply incl_charac_to with s1; assumption.
Qed.

Lemma inter_universal : forall (a b:Type) (r s t:R a b),
    t <= (r /\ s) <-> t <= r /\ t <= s.
Proof.
    intros a b r s t. split.
    - intros H1. split. 
        + apply incl_trans with (r /\ s); try assumption. apply incl_inter_l.
        + apply incl_trans with (r /\ s); try assumption. apply incl_inter_r.
    - intros [H1 H2]. unfold inter. apply incl_charac. intros x y. 
      intros H3. split; apply incl_charac_to with t; assumption.
Qed.

Lemma conv_incl : forall (a b:Type) (r s:R a b), 
    r <= s -> conv r <= conv s.
Proof.
    intros a b r s H1. apply incl_charac. intros x y. unfold conv.
    apply incl_charac_to. assumption.
Qed.

