Require Import nat.
Require Import bool.
Require Import setoid.

Inductive Key : Type := key : nat -> Key.

Definition beq_Key (k1 k2:Key) : bool :=
    match k1, k2 with
    | key n1, key n2    => eqb n1 n2
    end.

Lemma beq_Key_refl : forall (k:Key), beq_Key k k = true.
Proof. intros [n]. apply eqb_refl. Qed.

    
Lemma beq_Key_true_iff : forall (k1 k2:Key),
    beq_Key k1 k2 = true <-> k1 = k2.
Proof.
    intros [n1] [n2]. split.
    - simpl. intros H. rewrite <- eqb_semantics in H. rewrite H. reflexivity.
    - intros H. inversion H. apply eqb_refl.
Qed.

Lemma beq_Key_false_iff : forall (k1 k2:Key),
    beq_Key k1 k2 = false <-> k1 <> k2.
Proof.
    intros [n1] [n2]. split.
    - simpl. intros H. rewrite eqb_false_iff in H. 
        intros H'. inversion H' as [H0]. apply H. exact H0.
    - simpl. intros H. apply eqb_false_iff. intros H'. apply H.
        rewrite H'. reflexivity.
Qed.

Definition TotalMap (a:Type) : Type := Key -> a.

Definition t_empty (a:Type) (v:a) : TotalMap a := fun _ => v.

Arguments t_empty {a} _.


Definition t_update (a:Type) (m:TotalMap a) (k:Key) (v:a) :=
    fun k' => if beq_Key k k' then v else m k'.

Arguments t_update {a} _ _ _.




