Require Import list.

Parameter a : Type.

Parameter eq_proof : forall (x y:a), option (x = y).

Axiom eq_proof_correct : forall (x y:a),
    x = y <-> eq_proof x y <> None.

Inductive subseq : list a -> list a -> Prop :=
    | nil_sub       : forall (l:list a), subseq [] l
    | cons_sub      : forall (l k: list a) (x:a), subseq l k -> subseq (x::l) (x::k) 
    | extend_sub    : forall (l k: list a) (x:a), subseq l k -> subseq l (x::k) 
    .


Theorem subseq_refl : forall (l: list a), subseq l l.
Proof.
    induction l as [|x xs H].
    - apply nil_sub.
    - apply cons_sub. exact H.
Qed.

Theorem subseq_app : forall (l k m: list a),
    subseq l k -> subseq l (k ++ m).
Proof.
    intros l k m H. induction H as [l IH|l k x H IH|l k x H IH].
    - apply nil_sub.
    - simpl. apply cons_sub. exact IH.
    - simpl. apply extend_sub. apply IH.
Qed.

Theorem subseq_trans : forall (l k m: list a),
    subseq l k -> subseq k m -> subseq l m.
Proof.
    intros l k m Hlk. revert m.
    induction Hlk as [l|l k x H IH|l k x H IH].
    - intros. apply nil_sub.
    - intros m Hkm. set (k' := x::k). fold k' in Hkm.
        assert (k' = x::k) as Hk. { auto. }
        generalize Hk, IH, H.
        induction Hkm as [r|r m y H' IH'|r m y H' IH'].
        + inversion Hk.
        + intros H0 H1 H2. inversion H0. apply cons_sub.
            apply H1. rewrite <- H5. exact H'.
        + intros H0 H1 H2. apply extend_sub. apply IH'.
            { exact Hk. }
            { exact Hk. }
            { exact H1. }
            { exact H2. }
    - intros m Hkm. set (k' := x::k). fold k' in Hkm.
        assert (k' = x::k) as Hk. { auto. }
        generalize Hk, IH, H.
        induction Hkm as [r|r m y H' IH'|r m y H' IH'].
        + inversion Hk.
        + intros H0 H1 H2. inversion Hk as [H3].
            apply extend_sub. apply H1. rewrite <- H4. exact H'.
        + intros H0 H1 H2. apply extend_sub. apply IH'.
            { exact Hk. }
            { exact Hk. }
            { exact H1. }
            { exact H2. }
Qed.



