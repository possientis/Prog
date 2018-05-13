Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.
Require Import transform.


Theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp.
Proof.
    intros a e. 
    induction a; try (reflexivity);
    destruct (fold_constants_aexp a1) eqn:E1, (fold_constants_aexp a2) eqn:E2;
    try (simpl; rewrite E1, E2, IHa1, IHa2; reflexivity).
Qed.


Theorem fold_constants_bexp_sound :btrans_sound fold_constants_bexp.
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
 
