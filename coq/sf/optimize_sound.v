Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.
Require Import transform.
Require Import optimize.

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

(*
Theorem optimize_0plus_bexp_sound : btrans_sound optimize_0plus_bexp.
Proof.
    unfold btrans_sound, bequiv.
    intros b. induction b as [| |a1 a2|a1 a2|b1 IH1|b1 IH1 b2 IH2].
    - reflexivity.
    - reflexivity.
    - simpl. intros env. 
        rewrite (optimize_0plus_aexp_sound a1), (optimize_0plus_aexp_sound a2).
        reflexivity.
    - simpl. intros env.
        rewrite (optimize_0plus_aexp_sound a1), (optimize_0plus_aexp_sound a2).
        reflexivity.
    - simpl. intros env. rewrite IH1. reflexivity.
    - simpl. intros env. rewrite IH1, IH2. reflexivity.
Qed.


Theorem optimize_0plus_com_sound: ctrans_sound optimize_0plus_com.
Proof.
    apply ctrans_is_sound.
    - apply optimize_0plus_aexp_sound.
    - apply optimize_0plus_bexp_sound.
Qed.
*)
