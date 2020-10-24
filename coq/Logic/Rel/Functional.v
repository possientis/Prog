Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Composition.


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

