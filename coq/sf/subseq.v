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

(*
Theorem subseq_trans : forall (l k m: list a),
    subseq l k -> subseq k m -> subseq l m.
Proof.

Show.
*)

