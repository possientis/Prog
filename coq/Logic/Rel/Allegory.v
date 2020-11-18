Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Func.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Shunting.
Require Import Logic.Rel.Composition.

Lemma incl_function : forall (a b:Type) (f g:R a b),
    Function f -> Function g -> f <= g -> f = g.
Proof.
    intros a b f g H1 H2 H3. apply incl_anti; try assumption.
    rewrite <- (conv_conv _ _ f). rewrite <- (conv_conv _ _ g). 
    apply incl_conv. rewrite <- (id_left _ _ (conv g)). 
    apply shunting_rule_right; try assumption.
    apply shunting_rule_left; try assumption.
    rewrite id_right. assumption.
Qed.

