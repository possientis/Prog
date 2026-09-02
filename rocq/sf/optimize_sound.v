Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.
Require Import transform.
Require Import optimize.
Require Import fold_constants.
Require Import fold_constants_sound.

Theorem optimize_0plus_aexp_sound : atrans_sound optimize_0plus_aexp.
Proof. 
    unfold atrans_sound, aequiv.
    intros a. induction a as [n|k|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2]. 
    - reflexivity.
    - reflexivity.
    - simpl. intros env. destruct a1 as [[|n]|[n]|b1 b2|b1 b2|b1 b2]; 
        simpl; 
        simpl in IH1;
        try rewrite IH1;
        rewrite IH2;
        reflexivity.
    - simpl. intros env. rewrite IH1, IH2. reflexivity.
    - simpl. intros env. rewrite IH1, IH2. reflexivity. 
Qed.

Theorem optimize_0plus_bexp_sound : btrans_sound optimize_0plus_bexp.
Proof. apply btrans_is_sound. apply optimize_0plus_aexp_sound. Qed.

Theorem optimize_0plus_com_sound: ctrans_sound optimize_0plus_com.
Proof.
    apply ctrans_is_sound.
    - apply optimize_0plus_aexp_sound.
    - apply optimize_0plus_bexp_sound.
Qed.

Theorem optimize_aexp_sound : atrans_sound optimize_aexp.
Proof.
    apply (compose_aexp_sound fold_constants_aexp).
    - apply fold_constants_aexp_sound.
    - apply optimize_0plus_aexp_sound.
Qed.

Theorem optimize_bexp_sound : btrans_sound optimize_bexp.
Proof. apply btrans_is_sound. apply optimize_aexp_sound. Qed.

Theorem optimize_com_sound : ctrans_sound optimize_com.
Proof. 
    apply ctrans_is_sound.
    - apply optimize_aexp_sound.
    - apply optimize_bexp_sound.
Qed.



