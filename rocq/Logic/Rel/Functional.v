Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Domain.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Composition.

(* A Functional relation is known as a 'simple arrow' in the book AOP           *)

Definition Functional (a b:Type) (r:R a b) : Prop := r ; conv r <= id.

Arguments Functional {a} {b}.

Lemma Functional_charac : forall (a b:Type) (r:R a b),
    Functional r <-> forall (x:a) (y y':b), r x y -> r x y' -> y = y'.
Proof.
    intros a b r. unfold Functional. split; intros H1.
    - intros x y y' H2 H3. assert ((r ; conv r) y y') as H4.
        { exists x. split; assumption. }
      apply (incl_charac_to _ _ (r ; conv r) _ y y') in H1; try assumption.
      destruct H1 as [y]. reflexivity.
    - apply incl_charac. intros y y'. intros [x [H2 H3]].
      rewrite (H1 x y y'); try assumption. constructor.
Qed.

Lemma comp_distrib_inter_r : forall (a b c:Type) (t:R a b) (r s:R b c),
    Functional t -> (r /\ s) ; t = ((r ; t) /\ (s ; t)).
Proof.
    intros a b c t r s H1. apply incl_anti.
    - apply comp_semi_distrib_inter_r.
    - apply incl_charac. intros x y [[z' [H2 H3]] [z [H4 H5]]].
      assert (z' = z) as H6.
        { destruct (Functional_charac a b t) as [H6 H7].
          apply (H6 H1) with x; assumption. }
      subst. exists z. split; try assumption. split; assumption.
Qed.

Lemma Functional_conv : forall (a b:Type) (r:R a b),
    Functional r -> r = r ; conv r ; r.
Proof.
    intros a b r H1. apply Ext. intros x y. split; intros H2.
    - exists x. split; try assumption. exists y. split; assumption.
    - destruct H2 as [z [[u [H2 H3]] H4]]. assert (y = u) as H5.
        { destruct (Functional_charac a b r) as [H6 H7].
          apply H6 with z; assumption. }
      subst. assumption.
Qed.

Lemma dom_ex4_17 : forall (a b c:Type) (r:R a b) (s:R b c),
    Functional r -> dom s ; r = r ; dom (s ; r).
Proof.
    intros a b c r s H0. apply Ext. intros x y. split; intros H1.
    - destruct H1 as [z [H1 H2]]. destruct H2 as [y [z H2]].
      exists x. split; try assumption. constructor. exists z. exists y.
      split; assumption.
    - destruct H1 as [z [H1 H2]]. destruct H1 as [x [z [y' [H1 H3]]]]. 
      assert (y' = y) as H4.
        { destruct (Functional_charac a b r) as [H5 H6].
          apply H5 with x; assumption. }
      subst. exists y. split; try assumption. constructor. exists z. assumption.
Qed.
