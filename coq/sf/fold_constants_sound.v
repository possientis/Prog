Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.
Require Import transform.
Require Import fold_constants.


Theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp.
Proof.
    intros a e. 
    induction a; try (reflexivity);
    destruct (fold_constants_aexp a1) eqn:E1, (fold_constants_aexp a2) eqn:E2;
    try (simpl; rewrite E1, E2, IHa1, IHa2; reflexivity).
Qed.


Theorem fold_constants_bexp_sound : btrans_sound fold_constants_bexp.
Proof. apply btrans_is_sound. apply fold_constants_aexp_sound. Qed.


Theorem fold_constants_com_sound: ctrans_sound fold_constants_com.
Proof. 
    apply ctrans_is_sound.
    - apply fold_constants_aexp_sound.
    - apply fold_constants_bexp_sound.
Qed.


