Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.

Definition atrans_sound (atrans:aexp -> aexp) : Prop :=
    forall (a:aexp), aequiv a (atrans a).

Definition btrans_sound (btrans:bexp -> bexp) : Prop :=
    forall (b:bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans:com -> com) : Prop :=
    forall (c:com), cequiv c (ctrans c).

Fixpoint btrans (fa:aexp -> aexp) (b:bexp) : bexp :=
    match b with
    | BTrue         => BTrue
    | BFalse        => BFalse
    | BEq a1 a2     =>
        match (fa a1, fa a2) with
        | (ANum n1, ANum n2)        => if eqb n1 n2 then BTrue else BFalse
        | (a1', a2')                => BEq a1' a2'
        end
    | BLe a1 a2     =>
        match (fa a1, fa a2) with
        | (ANum n1, ANum n2)        => if leb n1 n2 then BTrue else BFalse
        | (a1', a2')                => BLe a1' a2'
        end
    | BNot b1       =>
        match (btrans fa b1) with
        | BTrue     => BFalse
        | BFalse    => BTrue
        | b1'       => BNot b1'
        end
    | BAnd b1 b2    =>
        match (btrans fa b1, btrans fa b2) with
        | (BTrue, BTrue)    => BTrue
        | (BTrue, BFalse)   => BFalse
        | (BFalse, BTrue)   => BFalse
        | (BFalse, BFalse)  => BFalse
        | (b1', b2')        => BAnd b1' b2'
        end
    end.

Fixpoint ctrans (fa:aexp -> aexp)(fb:bexp -> bexp)(c:com) : com :=
    match c with
    | SKIP          => SKIP
    | k ::= a       => k ::= (fa a)
    | c1 ;; c2      => (ctrans fa fb c1) ;; (ctrans fa fb c2)
    | CIf b c1 c2   => match (fb b) with
                       | BTrue      => ctrans fa fb c1
                       | BFalse     => ctrans fa fb c2
                       | b'         => CIf b' (ctrans fa fb c1)
                                              (ctrans fa fb c2)
                       end
    | CWhile b c1   => match (fb b) with
                       | BTrue      => CWhile BTrue SKIP (* oo-loop all the same *)
                       | BFalse     => SKIP
                       | b'         => CWhile b' (ctrans fa fb c1)
                       end
    end.

Theorem ctrans_is_sound : forall (fa:aexp -> aexp) (fb:bexp -> bexp), 
    atrans_sound fa -> btrans_sound fb -> ctrans_sound (ctrans fa fb).
Proof.
    intros fa fb Ha Hb. unfold ctrans_sound. intros c. induction c;
    try (apply refl_cequiv);
    try (apply CAss_congruence; apply Ha);
    try (apply CSeq_congruence; assumption).
    - destruct (fb b) eqn:E; simpl;
        try (rewrite E; apply CIf_congruence; 
                try (assumption);
                try (rewrite <- E; apply Hb)
            ).
        + apply trans_cequiv with c1.
            { apply if_true. rewrite <- E. apply Hb. }
            { rewrite E. assumption. }
        + apply trans_cequiv with c2.
            { apply if_false. rewrite <- E. apply Hb. }
            { rewrite E. assumption. }
    - destruct (fb b) eqn:E; simpl; rewrite E;
        try ( apply CWhile_congruence; try (assumption);
              rewrite <- E; apply Hb
            ).
        + apply while_true. rewrite <- E. apply Hb.
        + apply while_false. rewrite <- E. apply Hb.
Qed.

Theorem btrans_is_sound : forall (fa:aexp -> aexp), 
    atrans_sound fa -> btrans_sound (btrans fa).
Proof.
    intros fa Ha b e. induction b; 
    try (reflexivity).
    - simpl; rename a into a1; rename a0 into a2;
      destruct (fa a1) eqn:E1, (fa a2) eqn:E2;
      try (rewrite <- E1, <- E2, (Ha a1), (Ha a2); reflexivity).
      rewrite (Ha a1), (Ha a2), E1, E2; simpl; destruct (eqb n n0); reflexivity.
    - simpl; rename a into a1; rename a0 into a2;
      destruct (fa a1) eqn:E1, (fa a2) eqn:E2;
      try (rewrite <- E1, <- E2, (Ha a1), (Ha a2); reflexivity).
      rewrite (Ha a1), (Ha a2), E1, E2; simpl; destruct (leb n n0); reflexivity.
    - simpl. destruct (btrans fa b); rewrite IHb; reflexivity.
    - simpl. destruct (btrans fa b1), (btrans fa b2); rewrite IHb1, IHb2;
        reflexivity.
Qed.


