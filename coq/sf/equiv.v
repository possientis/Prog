Require Import bool.
Require Import syntax.
Require Import eval.
Require Import dictionary.
Require Import state.


Definition aequiv (a1 a2:aexp) : Prop :=
  forall (e:State), aeval e a1 = aeval e a2.

Definition bequiv (b1 b2:bexp) : Prop :=
  forall (e:State), beval e b1 = beval e b2.

Definition cequiv (c1 c2:com)  : Prop :=
  forall (e e':State), ceval c1 e e' <-> ceval c2 e e'. 


Theorem skip_left : forall (c:com), cequiv (SKIP ;; c) c.
Proof.
    intros c e e'. split.
    - intros H. inversion H. subst. inversion H2. subst. assumption.
    - intros H. simpl. apply E_Seq with e.
        + constructor.
        + assumption.
Qed.

Theorem skip_right : forall (c:com), cequiv (c ;; SKIP) c.
Proof.
    intros c e e'. split.
    - intros H. inversion H. subst. inversion H5. subst. assumption.
    - intros H. simpl. apply E_Seq with e'.
        + assumption.
        + constructor.
Qed.

Theorem if_true_simple : forall (c1 c2:com), 
    cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1.
Proof.
    intros c1 c2 e e'. split.
    - intros H. inversion H; subst.
        + assumption.
        + inversion H5.
    - intros H. apply E_IfTrue.
        + reflexivity.
        + assumption.
Qed.
    
Theorem if_true : forall (b:bexp) (c1 c2:com),
    bequiv b BTrue -> cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
    intros b c1 c2 H e e'. unfold bequiv in H. simpl in H. split.
    - intros H'. inversion H'; subst.
        + assumption.
        + rewrite (H e) in H5. inversion H5. 
    - intros H'. apply E_IfTrue.
        + apply H.
        + assumption.
Qed.

Theorem if_false : forall (b:bexp) (c1 c2:com),
    bequiv b BFalse -> cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
    intros b c1 c2 H e e'. unfold bequiv in H. simpl in H. split.
    - intros H'. inversion H'; subst.
        + rewrite (H e) in H5. inversion H5. 
        + assumption.
    - intros H'. apply E_IfFalse.
        + apply H.
        + assumption.
Qed.

Theorem swap_if_branches : forall (b:bexp) (c1 c2:com),
    cequiv (IFB b THEN c1 ELSE c2 FI) (IFB (BNot b) THEN c2 ELSE c1 FI).
Proof.
    intros b c1 c2 e e'. split.
    - intros H. inversion H; subst.
        + apply E_IfFalse.
            { simpl. rewrite H5. reflexivity. }
            { assumption. }
        + apply E_IfTrue.
            { simpl.  rewrite H5. reflexivity. }
            { assumption. }
    - intros H. inversion H; subst.
        + apply E_IfFalse.
            { simpl in H5. destruct (beval e b).
                { inversion H5. }
                { reflexivity. } }
            { assumption. }
        + apply E_IfTrue.
            { simpl in H5. destruct (beval e b).
                { reflexivity. }
                { inversion H5. } }
            { assumption. }
Qed.


Theorem while_false : forall (b:bexp) (c:com),
    bequiv b BFalse -> cequiv (WHILE b DO c END) SKIP.
Proof.
    intros b c H e e'. unfold bequiv in H. simpl in H. split.
    - intros H'. inversion H'; subst.
        + constructor.
        + rewrite (H e) in H2. inversion H2.
    - intros H'. inversion H'. subst. constructor. apply H.
Qed.


