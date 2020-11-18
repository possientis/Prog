Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Functional.
Require Import Logic.Rel.Composition.

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

Lemma modularity_law_l_func : forall (a b c:Type) (r:R a b) (s:R b c) (t:R a c),
    Functional s -> ((s ; r) /\ t) = s ; (r /\ (conv s ; t)).  
Proof.
    intros a b c r s t H1. apply incl_anti. 
    - apply modularity_law_l.
    - apply incl_trans with ((s ; r) /\ (s ; (conv s ; t))).
        + apply comp_semi_distrib_inter_l.
        + rewrite <- comp_assoc. apply incl_inter_compat_r.
          apply incl_trans with (id ; t).
            { apply incl_comp_compat_l. apply H1. }
            { rewrite id_left. apply incl_refl. } 
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


