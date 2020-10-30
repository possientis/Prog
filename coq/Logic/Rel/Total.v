Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Domain.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
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
