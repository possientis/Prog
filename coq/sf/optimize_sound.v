Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import optimize.
Require Import state.



Theorem optimize_0plus_aexp_sound : forall (a:aexp) (env:State), 
    aeval env (optimize_0plus_aexp a) = aeval env a.
Proof.
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


Theorem optimize_0plus_bexp_sound : forall (b:bexp) (env:State),
   beval env (optimize_0plus_bexp b) = beval env b.
Proof.
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
