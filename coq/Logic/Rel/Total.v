Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Domain.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Coreflexive.
Require Import Logic.Rel.Composition.


Definition Total (a b:Type) (r:R a b) : Prop := id <= conv r ; r.

Arguments Total {a} {b}.

Lemma Total_charac : forall (a b:Type) (r:R a b),
    Total r <-> forall (x:a), exists (y:b), r x y.
Proof.
    intros a b r. split; intros H1.
    - intros x. unfold Total in H1. apply (incl_charac_to _ _ id _ x x) in H1.
        + destruct H1 as [y [H1 H2]]. exists y. assumption.
        + constructor.
    - apply incl_charac. intros x y H2. destruct H2 as [x].
      destruct (H1 x) as [y H2]. exists y. split; assumption.
Qed.

Lemma Total_dom : forall (a b:Type) (r:R a b),
    Total r <-> dom r = id.
Proof.
    intros a b r. split; intros H1.
    - apply incl_anti. 
        + apply dom_corefl.
        + apply incl_charac. intros x y H2. destruct H2 as [x].
          constructor. apply Total_charac. assumption.
    - apply Total_charac. intros x. assert (dom r x x) as H2.
        { rewrite H1. constructor. }
      destruct H2 as [x [y H2]]. exists y. assumption. 
Qed.

Lemma Total_dom' : forall (a b:Type) (r:R a b),
    Total r <-> id <= dom r.
Proof.
    intros a b r. split; intros H1.
    - apply Total_dom in H1. rewrite H1. apply incl_refl.
    - apply Total_dom. symmetry. apply corefl_id.
        + apply dom_corefl.
        + assumption.
Qed.

Lemma Total_comp : forall (a b c:Type) (r:R a b) (s:R b c),
    Total (s ; r) -> Total r.
Proof.
    intros a b c r s H1. apply Total_dom'. apply Total_dom in H1.
    rewrite <- H1. apply dom_comp_incl.
Qed.

Lemma Total_incl : forall (a b:Type) (r s:R a b), 
    Total r -> r <= s -> Total s.
Proof.
    intros a b r s H1 H2. apply Total_dom'. apply Total_dom in H1.
    rewrite <- H1. apply dom_incl_compat. assumption.
Qed.

(*
Lemma Total_inter : forall (a b:Type) (r s:R a b),
    Total (r /\ s) <-> id <= conv r ; s.
Proof.
    intros a b r s. split; intros H1.
    - destruct (Total_charac a b (r /\ s)) as [H2 H3].
      remember (H2 H1) as H4 eqn:E. clear E H1 H2 H3.
      apply incl_charac. intros x y H1. destruct H1 as [x].
      destruct (H4 x) as [y [H1 H2]]. exists y. split; assumption.
    - apply Total_charac. intros x.
Show.
*)

