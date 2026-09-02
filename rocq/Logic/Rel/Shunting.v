Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Include.
Require Import Logic.Rel.Function.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Composition.

Lemma shunting_rule_left : 
    forall (a b c:Type) (r:R a b) (f:R b c) (s:R a c), Function f -> 
        f ; r <= s <-> r <= conv f ; s.
Proof.
    intros a b c r f s [H1 H2]. split; intros H3.
    - apply incl_trans with ((conv f; f) ; r).
        + remember ((conv f; f) ; r) as e eqn:E. rewrite <- (id_left _ _ r). 
          rewrite E. clear e E. apply incl_comp_compat_l. assumption.
        + rewrite comp_assoc. apply incl_comp_compat_r. assumption.
    - apply incl_trans with ((f ; conv f) ; s).
        + rewrite comp_assoc. apply incl_comp_compat_r. assumption.
        + remember ((f ; conv f) ; s) as e eqn:E. rewrite <- (id_left _ _ s).
          rewrite E. clear e E. apply incl_comp_compat_l. assumption.
Qed.

Lemma shunting_rule_right :
    forall (a b c:Type) (f:R b a) (r:R b c) (s:R a c), Function f ->
        r ; conv f <= s <-> r <= s ; f.
Proof.
    intros a b c f r s [H1 H2]. split; intros H3.
    - apply incl_trans with (r; (conv f; f)).
        + remember (r ; (conv f; f)) as e eqn:E. rewrite <- (id_right _ _ r).
          rewrite E. clear e E. apply incl_comp_compat_r. assumption.
        + rewrite <- comp_assoc. apply incl_comp_compat_l. assumption.
    - apply incl_trans with (s; (f ; conv f)).
        + rewrite <- comp_assoc. apply incl_comp_compat_l. assumption.
        + remember (s ; (f ; conv f)) as e eqn:E. rewrite <- (id_right _ _ s).
          rewrite E. clear e E. apply incl_comp_compat_r. assumption.
Qed.

Lemma shunting_rev_left : forall (b c:Type) (f:R b c),
    (forall (a:Type) (r:R a b) (s:R a c), f ; r <= s <-> r <= conv f ; s) -> 
    Function f.
Proof.
    intros b c f H1. split.
    - apply (H1 _ (conv f) id). rewrite id_right. apply incl_refl.
    - apply (H1 _ id f). rewrite id_right. apply incl_refl.
Qed.

Lemma shunting_rev_right : forall (a b:Type) (f:R b a),
    (forall (c:Type) (r:R b c) (s:R a c), r ; conv f <= s <-> r <= s ; f) -> 
    Function f.
Proof.
    intros a b f H1. split.
   - apply (H1 _ f id). rewrite id_left. apply incl_refl. 
   - apply (H1 _ id (conv f)). rewrite id_left. apply incl_refl.
Qed.


