Require Import nat.
Require Import bool.
Require Import syntax.
Require Import eval.
Require Import state.


Inductive aevalR:State -> aexp -> nat -> Prop :=
| E_ANum  : forall e n, aevalR e (ANum n) n
| E_AKey  : forall e k, aevalR e (AKey k) (e k)
| E_APlus : forall e n1 n2 a1 a2, 
    aevalR e a1 n1 -> aevalR e a2 n2 -> aevalR e (APlus  a1 a2) (n1 + n2)
| E_AMinus: forall e n1 n2 a1 a2, 
    aevalR e a1 n1 -> aevalR e a2 n2 -> aevalR e (AMinus a1 a2) (n1 - n2)
| E_AMult : forall e n1 n2 a1 a2, 
    aevalR e a1 n1 -> aevalR e a2 n2 -> aevalR e (AMult  a1 a2) (n1 * n2)
.

Inductive bevalR:State-> bexp -> bool -> Prop :=
| E_BTrue : forall e, bevalR e BTrue true
| E_BFalse: forall e, bevalR e BFalse false
| E_BEq   : forall e n1 n2 a1 a2, 
    aevalR e a1 n1 -> aevalR e a2 n2 -> bevalR e (BEq a1 a2) (eqb n1 n2) 
| E_BLe   : forall e n1 n2 a1 a2, 
    aevalR e a1 n1 -> aevalR e a2 n2 -> bevalR e (BLe a1 a2) (leb n1 n2)
| E_BNot  : forall e b1 e1, 
    bevalR e e1 b1 -> bevalR e (BNot e1) (negb b1)
| E_BAnd  : forall e b1 b2 e1 e2,
    bevalR e e1 b1 -> bevalR e e2 b2 -> bevalR e (BAnd e1 e2) (andb b1 b2) 
.

Theorem aeval_iff_aevalR : forall (env:State) (a:aexp) (n:nat),
    aevalR env a n <-> aeval env a = n.
Proof.
    intros env a n. split.
    - intro H. induction H as   [ n
                                | k
                                | e n1 n2 a1 a2 H1 IH1 H2 IH2
                                | e n1 n2 a1 a2 H1 IH1 H2 IH2
                                | e n1 n2 a1 a2 H1 IH1 H2 IH2
                                ].
        + reflexivity.
        + reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.
        + simpl. rewrite IH1, IH2. reflexivity.

    - revert n env. induction a as [n|k|a1 H1 a2 H2| a1 H1 a2 H2| a1 H1 a2 H2].
        + simpl. intros p e H. subst. apply E_ANum.
        + simpl. intros p e H. subst. apply E_AKey.
        + simpl. intros p e H. subst. apply E_APlus. 
            { apply H1. reflexivity. }
            { apply H2. reflexivity. }
        + simpl. intros p e H. subst. apply E_AMinus. 
            { apply H1. reflexivity. }
            { apply H2. reflexivity. }
        + simpl. intros p e H. subst. apply E_AMult. 
            { apply H1. reflexivity. }
            { apply H2. reflexivity. }
Qed.

Theorem aeval_iff_aevalR' : forall (env:State) (a:aexp) (n:nat),
    aevalR env a n <-> aeval env a = n.
Proof. 
    split. 
    - intros H. induction H; subst; reflexivity.
    - revert n env. induction a as [n|k|a1 H1 a2 H2| a1 H1 a2 H2| a1 H1 a2 H2]; 
        simpl; intros; subst; constructor; 
        try apply H1; try apply H2; reflexivity.  
Qed.


Theorem beval_iff_bevalR : forall (env:State) (e:bexp) (b:bool),
    bevalR env e b <-> beval env e = b.
Proof.
    split.
    - intros H. induction H; subst; try reflexivity; simpl.
        + assert (aeval e a1 = n1) as H1. 
            { apply aeval_iff_aevalR. assumption. }
          assert (aeval e a2 = n2) as H2. 
            { apply aeval_iff_aevalR. assumption. }
           rewrite H1, H2. reflexivity.
        +  assert (aeval e a1 = n1) as H1. 
            { apply aeval_iff_aevalR. assumption. }
           assert (aeval e a2 = n2) as H2. 
               { apply aeval_iff_aevalR. assumption. }
           rewrite H1, H2. reflexivity.
    - revert b. induction e as [ | |a1 a2|a1 a2|e1 H1|e1 H1 e2 H2];
        intros; subst; simpl; constructor; try apply aeval_iff_aevalR; 
        try reflexivity; try apply H1; try apply H2; reflexivity.
Qed.
