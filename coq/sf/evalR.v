Require Import nat.
Require Import bool.
Require Import syntax.
Require Import eval.

(*

Reserved Notation "e 'a=>' n" (at level 90, no associativity).

Inductive aevalR:aexp -> nat -> Prop :=
| E_ANum  : forall n, (ANum n) a=> n
| E_APlus : forall n1 n2 a1 a2, a1 a=> n1 -> a2 a=> n2 -> APlus  a1 a2 a=> n1 + n2
| E_AMinus: forall n1 n2 a1 a2, a1 a=> n1 -> a2 a=> n2 -> AMinus a1 a2 a=> n1 - n2
| E_AMult : forall n1 n2 a1 a2, a1 a=> n1 -> a2 a=> n2 -> AMult  a1 a2 a=> n1 * n2

where "e 'a=>' n" := (aevalR e n).

Reserved Notation "e 'b=>' b" (at level 90, no associativity).

Inductive bevalR:bexp -> bool -> Prop :=
| E_BTrue : BTrue   b=> true
| E_BFalse: BFalse  b=> false
| E_BEq   : forall n1 n2 a1 a2, a1 a=> n1 -> a2 a=> n2 -> BEq a1 a2 b=> eqb n1 n2 
| E_BLe   : forall n1 n2 a1 a2, a1 a=> n1 -> a2 a=> n2 -> BLe a1 a2 b=> leb n1 n2 
| E_BNot  : forall b1 e1, e1 b=> b1 -> BNot e1 b=> negb b1
| E_BAnd  : forall b1 b2 e1 e2,e1 b=> b1 -> e2 b=> b2 -> BAnd e1 e2 b=> andb b1 b2 

where "e 'b=>' b" := (bevalR e b).

Theorem aeval_iff_aevalR : forall (a:aexp) (n:nat),
    a a=> n <-> aeval a = n.
Proof.
    intros a n. split.
    - intro H. induction H as   [ n
                                | n1 n2 a1 a2 H1 IH1 H2 IH2
                                | n1 n2 a1 a2 H1 IH1 H2 IH2
                                | n1 n2 a1 a2 H1 IH1 H2 IH2
                                ].
        + reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
    - revert n. induction a as [n|a1 H1 a2 H2| a1 H1 a2 H2| a1 H1 a2 H2].
        + simpl. intros p H. subst. apply E_ANum.
        + simpl. intros p H. subst. apply E_APlus. 
            { apply H1. reflexivity. }
            { apply H2. reflexivity. }
        + simpl. intros p H. subst. apply E_AMinus. 
            { apply H1. reflexivity. }
            { apply H2. reflexivity. }
        + simpl. intros p H. subst. apply E_AMult. 
            { apply H1. reflexivity. }
            { apply H2. reflexivity. }
Qed.


Theorem aeval_iff_aevalR' : forall (a:aexp) (n:nat),
    a a=> n <-> aeval a = n.
Proof. 
    split. 
    - intros H. induction H; subst; reflexivity.
    - revert n. induction a as [n|a1 H1 a2 H2| a1 H1 a2 H2| a1 H1 a2 H2]; 
        simpl; intros; subst; constructor; 
        try apply H1; try apply H2; reflexivity.  
Qed.

Theorem beval_iff_bevalR : forall (e:bexp) (b:bool),
    e b=> b <-> beval e = b.
Proof.
    split.
    - intros H. induction H; subst; try reflexivity; simpl.
        +  assert (aeval a1 = n1) as H1. { apply aeval_iff_aevalR. assumption. }
           assert (aeval a2 = n2) as H2. { apply aeval_iff_aevalR. assumption. }
           rewrite H1, H2. reflexivity.
        +  assert (aeval a1 = n1) as H1. { apply aeval_iff_aevalR. assumption. }
           assert (aeval a2 = n2) as H2. { apply aeval_iff_aevalR. assumption. }
           rewrite H1, H2. reflexivity.
    - revert b. induction e as [ | |a1 a2|a1 a2|e1 H1|e1 H1 e2 H2];
        intros; subst; simpl; constructor; try apply aeval_iff_aevalR; 
        try reflexivity; try apply H1; try apply H2; reflexivity.
Qed.
*)
