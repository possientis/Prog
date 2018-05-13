Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.
Require Import transform.
Require Import soundness.

(*
Theorem fold_constants_com_sound: ctrans_sound fold_constants_com.
Proof.
    intros c e e'. split.
    - intros H. induction H.
        + constructor.
        + simpl. replace n with (aeval e (fold_constants_aexp a)). 
            { constructor. reflexivity. }
          rewrite <- H. symmetry. apply fold_constants_aexp_sound. 
        + simpl. apply E_Seq with e'; assumption.
        + simpl. destruct (fold_constants_bexp b) eqn:E.
            { assumption. }
            { replace (beval e b) with (beval e (fold_constants_bexp b)) in H.
              rewrite E in H. simpl in H. inversion H. symmetry.
              apply fold_constants_bexp_sound. }
            { apply E_IfTrue.
                replace (beval e b) with (beval e (fold_constants_bexp b)) in H.
                rewrite E in H. assumption. symmetry. 
                apply fold_constants_bexp_sound.
                assumption. }
            { apply E_IfTrue.
                replace (beval e b) with (beval e (fold_constants_bexp b)) in H.
                rewrite E in H. assumption. symmetry. 
                apply fold_constants_bexp_sound.
                assumption. }
            { apply E_IfTrue.
                replace (beval e b) with (beval e (fold_constants_bexp b)) in H.
                rewrite E in H. assumption. symmetry. 
                apply fold_constants_bexp_sound.
                assumption. }
            { apply E_IfTrue.
                replace (beval e b) with (beval e (fold_constants_bexp b)) in H.
                rewrite E in H. assumption. symmetry. 
                apply fold_constants_bexp_sound.
                assumption. }
        +        

Show.

*)






