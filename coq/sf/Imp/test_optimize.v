Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import optimize.


Theorem optimize_0plus_sound : forall (a:aexp), 
    aeval (optimize_0plus a) = aeval a.
Proof.
    intros a. induction a as [n|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2]. 
    - reflexivity.
    - simpl. destruct a1 as [[|n]|b1 b2|b1 b2|b1 b2].
        + simpl. rewrite IH2. reflexivity.
        + simpl. rewrite IH2. reflexivity.
        + simpl. simpl in IH1. rewrite IH1. rewrite IH2. reflexivity.
        + simpl. simpl in IH1. rewrite IH1. rewrite IH2. reflexivity.
        + simpl. simpl in IH1. rewrite IH1. rewrite IH2. reflexivity.
    - simpl. rewrite IH1, IH2. reflexivity.
    - simpl. rewrite IH1, IH2. reflexivity. 
Qed.
    


Theorem optimize_0plus_sound2 : forall (a:aexp), 
    aeval (optimize_0plus a) = aeval a.
Proof.
    intros a. induction a as [n|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2]. 
    - reflexivity.
    - simpl. destruct a1 as [[|n]|b1 b2|b1 b2|b1 b2]; 
        simpl; 
        simpl in IH1;
        try rewrite IH1;
        rewrite IH2;
        reflexivity.
    - simpl. rewrite IH1, IH2. reflexivity.
    - simpl. rewrite IH1, IH2. reflexivity. 
Qed.


Theorem optimize_0plus_b_sound : forall (b:bexp),
   beval (optimize_0plus_b b) = beval b.
Proof.
    intros b. induction b as [| |a1 a2|a1 a2|b1 IH1|b1 IH1 b2 IH2].
    - reflexivity.
    - reflexivity.
    - simpl. rewrite (optimize_0plus_sound a1), (optimize_0plus_sound a2).
        reflexivity.
    - simpl. rewrite (optimize_0plus_sound a1), (optimize_0plus_sound a2).
        reflexivity.
    - simpl. rewrite IH1. reflexivity.
    - simpl. rewrite IH1, IH2. reflexivity.
Qed.


