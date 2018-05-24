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
Proof.
    intros b e. induction b; try (reflexivity); 
    try (
        simpl; rename a into a1, a0 into a2;
        destruct (fold_constants_aexp a1) eqn:E1, 
                 (fold_constants_aexp a2) eqn:E2;
         try (
            rewrite <- E1, <- E2; simpl;
            rewrite <- (fold_constants_aexp_sound a1), 
                    <- (fold_constants_aexp_sound a2);
            reflexivity
         )
    ).
        + rename n into n1, n0 into n2.
            rewrite (fold_constants_aexp_sound a1),
                    (fold_constants_aexp_sound a2).
            rewrite E1, E2. simpl.
            destruct (eqb n1 n2); simpl; reflexivity.
        + rename n into n1, n0 into n2.
            rewrite (fold_constants_aexp_sound a1),
                    (fold_constants_aexp_sound a2).
            rewrite E1, E2. simpl.
            destruct (leb n1 n2); simpl; reflexivity.
        + simpl. destruct (fold_constants_bexp b) eqn:E;
            try (rewrite IHb; reflexivity).
        + simpl.
          destruct (fold_constants_bexp b1) eqn:E1, 
                   (fold_constants_bexp b2) eqn:E2;
            try ( rewrite IHb1, IHb2; reflexivity ).
Qed.
 
Theorem fold_constants_com_sound: ctrans_sound fold_constants_com.
Proof.
    unfold ctrans_sound. intros c. induction c; simpl.
    - apply refl_cequiv.
    - apply CAss_congruence. apply fold_constants_aexp_sound.
    - apply CSeq_congruence; assumption.
    - destruct (fold_constants_bexp b) eqn:E. 
        + apply trans_cequiv with c1.
            { apply if_true. rewrite <- E. apply (fold_constants_bexp_sound). }
            { assumption. }
        + apply trans_cequiv with c2.
            { apply if_false. rewrite <- E. apply (fold_constants_bexp_sound). }
            { assumption. }
        + apply CIf_congruence; try (assumption).
            { apply trans_bequiv with (fold_constants_bexp b).
                { apply fold_constants_bexp_sound. }
                { rewrite E. apply refl_bequiv. } }
        + apply CIf_congruence; try (assumption).
            { apply trans_bequiv with (fold_constants_bexp b).
                { apply fold_constants_bexp_sound. }
                { rewrite E. apply refl_bequiv. } }
        + apply CIf_congruence; try (assumption).
            { apply trans_bequiv with (fold_constants_bexp b).
                { apply fold_constants_bexp_sound. }
                { rewrite E. apply refl_bequiv. } }
        + apply CIf_congruence; try (assumption).
            { apply trans_bequiv with (fold_constants_bexp b).
                { apply fold_constants_bexp_sound. }
                { rewrite E. apply refl_bequiv. } }
    - destruct (fold_constants_bexp b) eqn:E.             
        + apply while_true. rewrite <- E. apply fold_constants_bexp_sound.
        + apply while_false. rewrite <- E. apply fold_constants_bexp_sound.
        + apply CWhile_congruence.
            { rewrite <- E. apply fold_constants_bexp_sound. }
            { assumption. }
        + apply CWhile_congruence.
            { rewrite <- E. apply fold_constants_bexp_sound. }
            { assumption. }
        + apply CWhile_congruence.
            { rewrite <- E. apply fold_constants_bexp_sound. }
            { assumption. }
        + apply CWhile_congruence.
            { rewrite <- E. apply fold_constants_bexp_sound. }
            { assumption. }
Qed.
                    


