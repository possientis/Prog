Require Import bool.
Require Import list.
Require Import le.
Require Import In.
Require Import filter.

Inductive subseq (a:Type) : list a -> list a -> Prop :=
    | nil_sub       : forall (l:list a), subseq a [] l
    | cons_sub      : forall (l k: list a) (x:a), 
                        subseq a l k -> subseq a (x::l) (x::k) 
    | extend_sub    : forall (l k: list a) (x:a), subseq a l k -> subseq a l (x::k) 
    .

Arguments subseq {a} _ _.

Theorem subseq_refl : forall (a:Type) (l: list a), subseq l l.
Proof.
    induction l as [|x xs H].
    - apply nil_sub.
    - apply cons_sub. exact H.
Qed.


Theorem subseq_trans : forall (a:Type) (l k m: list a),
    subseq l k -> subseq k m -> subseq l m.
Proof.
    intros a l k m Hlk. revert m.
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

Theorem subseq_app : forall (a:Type) (l k m: list a),
    subseq l k -> subseq l (k ++ m).
Proof.
    intros a l k m H. induction H as [l|l k x H IH|l k x H IH].
    - apply nil_sub.
    - simpl. apply cons_sub. exact IH.
    - simpl. apply extend_sub. apply IH.
Qed.

Theorem subseq_length : forall (a:Type) (l k:list a),
    subseq l k -> length l <= length k.
Proof.
    intros a l k H. induction H as [l|l k x H IH|l k x H IH]. 
    - apply le_0_n.
    - simpl. apply n_le_m__Sn_le_Sm. exact IH.
    - simpl. apply le_S. exact IH.
Qed.

Theorem subseq_length_eq : forall (a:Type) (l k:list a),
    subseq l k -> length l = length k -> l = k.
Proof.
    intros a l k H. induction H as [l|l k x H IH|l k x H IH]. 
    - intros H. symmetry. apply length_0_iff_nil. symmetry. exact H.
    - intros H'. simpl in H'. inversion H' as [H0]. clear H'.
        assert (l = k) as H1. { apply IH. exact H0. }
        rewrite H1. reflexivity.
    - intros H'. exfalso. simpl in H'. apply subseq_length in H.
        rewrite H' in H. apply (not_le_Sn_n (length k)). exact H.
Qed.


Theorem subseq_antisym : forall (a:Type) (l k:list a),
    subseq l k -> subseq k l -> k = l.
Proof.
    intros a l k Hlk Hkl. apply subseq_length_eq.
    - exact Hkl.
    - apply le_antisym.
        +  apply subseq_length. exact Hkl.
        +  apply subseq_length. exact Hlk.
Qed.


Theorem filter_is_subseq : forall (a:Type) (test:a -> bool) (l:list a),
    subseq (filter test l) l.
Proof.
    intros a test l. induction l as [|x xs IH].
    - apply nil_sub.
    - simpl. destruct (test x).
        + apply cons_sub. exact IH.
        + apply extend_sub. exact IH.
Qed.




(* 'filter test l' is a subsequence of 'l' which satisfies predicate 
   'test' everywhere, and it is the longest such subsequence.
*)

Theorem filter_subseq : forall (a:Type) (test:a -> bool) (l:list a),
    subseq (filter test l) l                                /\
    (forall x, In x (filter test l) -> test x = true)       /\
    (forall k:list a, 
        subseq k l                          -> 
        (forall x, In x k -> test x = true) ->
        length k <= length (filter test l)).
Proof.
    intros a test l. split.
    - apply filter_is_subseq.
    - split.
        + apply filter_all_true.
        + intros k H. induction H as [l|l k x H IH|l k x H IH]. 
            { intros _. apply le_0_n. }
            { intros H'. assert (test x = true) as Hx.
                { apply H'. left. reflexivity. }
                simpl. rewrite Hx. simpl. apply n_le_m__Sn_le_Sm.
                    apply IH. intros y H0. apply H'. right. exact H0. 
            }
            { intros H'. destruct (test x) eqn:Hx.
                { simpl. rewrite Hx. simpl. apply le_S. apply IH. exact H'. }
                { simpl. rewrite Hx. apply IH. exact H'. }
            }
Qed.
    
   


