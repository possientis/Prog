Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Function.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Shunting.
Require Import Logic.Rel.Composition.


Lemma func_incl : forall (a b:Type) (f g:R a b),
    Function f -> Function g -> f <= g -> f = g.
Proof.
    intros a b f g H1 H2 H3. apply incl_anti; try assumption.
    rewrite <- (conv_conv _ _ f). rewrite <- (conv_conv _ _ g). 
    apply incl_conv. rewrite <- (id_left _ _ (conv g)). 
    apply shunting_rule_right; try assumption.
    apply shunting_rule_left; try assumption.
    rewrite id_right. assumption.
Qed.

(*
Lemma func_conv : forall (a b:Type) (r:R a b) (s:R b a),
    r ; s <= id -> id <= s ; r -> s = conv r.
Proof.
    intros a b r s H1 H2. apply incl_anti.
    - apply incl_trans with (conv r ; (r ; s)).
        + rewrite <- comp_assoc. apply incl_trans with (id ; s).
            {rewrite id_left. apply incl_refl. }
            { apply incl_comp_compat_l.
Show.
*)

