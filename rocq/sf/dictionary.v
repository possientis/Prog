Require Import Axiom_Extensionality.
Require Import nat.
Require Import bool.
Require Import option.
Require Import reflection.


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

Arguments t_empty {a} _ _.


Definition t_update (a:Type) (m:TotalMap a) (k:Key) (v:a) :=
    fun k' => if beq_Key k k' then v else m k'.

Arguments t_update {a} _ _ _ _.


Lemma t_update_eq : forall (a:Type) (m:TotalMap a) (k:Key) (v:a),
    (t_update m k v) k = v.
Proof.
    intros a m k v. unfold t_update. rewrite beq_Key_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (a:Type) (m:TotalMap a) (k1 k2:Key) (v:a),
    k1 <> k2 -> t_update m k1 v k2 = m k2.
Proof.
    intros a m k1 k2 v H. unfold t_update. 
    assert (beq_Key k1 k2 = false) as H'. { apply beq_Key_false_iff. exact H. }  
    rewrite H'. reflexivity.
Qed.

Lemma t_update_irrel : forall (a:Type) (m:TotalMap a) (k1 k2:Key),
    t_update m k1 (m k2) k2 = m k2.
Proof.
    intros a m k1 k2. destruct (beq_Key k1 k2) eqn:E.
    - rewrite beq_Key_true_iff in E. rewrite E. apply t_update_eq.
    - rewrite beq_Key_false_iff in E. apply t_update_neq. assumption. 
Qed.




Lemma t_update_shadow : forall (a:Type) (m:TotalMap a) (k:Key) (v1 v2:a),
    t_update (t_update m k v1) k v2 = t_update m k v2.
Proof.
    intros a m k v1 v2. apply extensionality. intros k'.
    destruct (beq_Key k k') eqn:H.
    - rewrite beq_Key_true_iff in H. 
        rewrite H, t_update_eq, t_update_eq. reflexivity.
    - rewrite beq_Key_false_iff in H. 
        rewrite t_update_neq, t_update_neq, t_update_neq.
        + reflexivity.
        + exact H.
        + exact H.
        + exact H.
Qed.


Lemma beq_KeyP : forall (x y:Key), reflect (x = y) (beq_Key x y).
Proof.
    intros x y. apply iff_reflect. symmetry. exact (beq_Key_true_iff x y).
Qed.


Lemma t_update_same : forall (a:Type) (m:TotalMap a) (k:Key),
    t_update m k (m k) = m.
Proof.
    intros a m k. apply extensionality. intros k'. destruct (beq_KeyP k k').
    - rewrite H. rewrite t_update_eq. reflexivity.
    - rewrite t_update_neq.
        + reflexivity.
        + exact H.
Qed.

Lemma t_update_permute : forall (a:Type) (m:TotalMap a) (k1 k2:Key) (v1 v2:a),
    k1 <> k2 -> 
    t_update (t_update m k2 v2) k1 v1 = 
    t_update (t_update m k1 v1) k2 v2.
Proof.
    intros a m k1 k2 v1 v2 H. apply extensionality. intros k.
    destruct (beq_KeyP k1 k) as [H1|H1], (beq_KeyP k2 k) as [H2|H2].
    - exfalso. apply H. rewrite H1, H2. reflexivity.
    - rewrite H1, t_update_eq. rewrite t_update_neq, t_update_eq.
        + reflexivity.
        + exact H2.
    - rewrite H2, t_update_eq. rewrite t_update_neq, t_update_eq.
        + reflexivity.
        + exact H1.
    - rewrite t_update_neq, t_update_neq, t_update_neq, t_update_neq.
        + reflexivity.
        + exact H1.
        + exact H2.
        + exact H2.
        + exact H1.
Qed.
    

Definition PartialMap (a:Type) : Type := TotalMap (option a).

Definition empty (a:Type) : PartialMap a := t_empty None.

Arguments empty {a} _.

Definition update (a:Type) (m:PartialMap a) (k:Key) (v:a) := t_update m k (Some v).

Arguments update {a} _ _ _ _.

Lemma update_eq : forall (a:Type) (m:PartialMap a) (k:Key) (v:a),
    (update m k v) k = Some v.
Proof. intros a m k v. unfold update. apply t_update_eq. Qed.

Lemma update_neq : forall (a:Type) (m:PartialMap a) (k k':Key) (v:a),
    k <> k' -> (update m k v) k' = m k'.
Proof. intros a m k k' v H. unfold update. apply t_update_neq. exact H. Qed.

Lemma update_shadow : forall (a:Type) (m:PartialMap a) (k:Key) (v1 v2:a),
    update (update m k v1) k v2 = update m k v2.
Proof. intros a m k v1 v2. unfold update. apply t_update_shadow. Qed.


Lemma update_same : forall (a:Type) (m:PartialMap a) (k:Key) (v:a),
    m k = Some v -> update m k v = m.
Proof. intros a m k v H. unfold update. rewrite <- H. apply t_update_same. Qed.

Lemma update_permute : forall (a:Type) (m:PartialMap a) (k1 k2:Key) (v1 v2:a),
    k1 <> k2 -> 
    update (update m k2 v2) k1 v1 =
    update (update m k1 v1) k2 v2.
Proof.
    intros a m k1 k2 v1 v2 H. unfold update. apply t_update_permute. exact H.
Qed.




