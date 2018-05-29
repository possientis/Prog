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







