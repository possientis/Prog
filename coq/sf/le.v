Require Import inductive_prop.
Require Import induction.
Require Import nat.
Require Import bool.


Module LEMODULE.

Inductive le : nat -> nat -> Prop :=
| le_n : forall (n:nat), le n n
| le_S : forall (n m:nat), le n m -> le n (S m)
.

Notation "n <= m" := (le n m).


Example test_le1 : 3 <= 3.
Proof. apply le_n. Qed.

Example test_le2 : 3 <= 6.
Proof. apply le_S, le_S, le_S, le_n. Qed. 

Definition lt (n m:nat) : Prop := le (S n) m.

End LEMODULE.



Inductive square_of : nat -> nat -> Prop :=
| sq : forall (n:nat), square_of n (n * n)
.

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall (n:nat), next_nat n (S n)
.

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall (n:nat), ev (S n) -> next_even n (S n)
| ne_2 : forall (n:nat), ev (S (S n)) -> next_even n (S (S n))
.


Inductive total_rel : nat -> nat -> Prop :=
| tr : forall (n m:nat), total_rel n m
.

Example test_total_rel1 : forall (n m:nat), total_rel n m.
Proof. intros n m. apply tr. Qed.

Inductive empty_rel : nat -> nat -> Prop := .

Example test_empty_rel : forall (n m:nat), ~ (empty_rel n m).
Proof. intros n m H. inversion H. Qed.


(* induction on proofs *)
Lemma le_trans : forall (n m p:nat), 
    n <= m -> m <= p -> n <= p.
Proof.
    intros n m p H. generalize p. clear p.
    induction H as [n'|n' H0 H'].
    - intros p H'. exact H'.
    - intros p H1. induction H1 as [p'| p' H2 H3].
        + apply H'. apply le_S, le_n.
        + apply le_S. exact H3.
Qed.

Lemma le_0_n : forall (n:nat), 0 <= n.
Proof. 
    induction n as [|n H].
    - apply le_n.
    - apply le_S. exact H.
Qed.

Theorem n_le_m__Sn_le_Sm : forall (n m:nat),
    n <= m -> S n <= S m.
Proof.
    intros n m H. induction H as [n'|n' m H'].
    - apply le_n.
    - apply le_S. exact H'.
Qed.

Theorem Sn_le_Sm__n_le_m : forall (n m:nat),
    S n <= S m -> n <= m.
Proof.
    intros n m H. inversion H as [H0|p H1].
    - apply le_n.
    - apply le_trans with (m := S n).
      +  apply le_S, le_n.
      +  auto. 
Qed.
        

Theorem le_plus_l : forall (n m: nat), n <= n + m.
Proof.
    intros n m. induction m as [|m H].
    - rewrite <- plus_n_O. apply le_n.
    - rewrite plus_n_Sm. apply le_S. exact H.
Qed.

Theorem plus_lt : forall (n m p:nat),
    n + m < p -> n < p /\ m < p.
Proof.
    intros n m p H. unfold lt in H. split.
    - unfold lt. apply le_trans with (m := S (n + m)).
        + rewrite <- plus_Sn_m. apply le_plus_l.
        + exact H.
    - unfold lt. apply le_trans with (m := S (n + m)).
        + rewrite plus_comm. rewrite <- plus_Sn_m. apply le_plus_l.
        + exact H.
Qed.


Theorem lt_S :  forall (n m:nat), n < m -> n < S m.
Proof.
    intros n m. unfold lt. intros H. apply le_S. exact H.
Qed.


Theorem leb_complete : forall (n m:nat),
    leb n m = true -> n <= m.
Proof.
    induction n as [|n H].
    - intros. apply le_0_n.
    - induction m as[|m H'].
        + simpl. intros H'. inversion H'.
        + simpl. intros H0. apply n_le_m__Sn_le_Sm. apply H. exact H0.
Qed.

Theorem leb_correct : forall (n m:nat),
    n <= m-> leb n m = true.
Proof.
    intros n m. generalize n. clear n. induction m as [|m H].
    - intros n H. inversion H. reflexivity.
    - induction n as [|n H'].
        + intros H'. reflexivity.
        + intros H0. simpl. apply Sn_le_Sm__n_le_m in H0. 
            apply H. exact H0.
Qed.

Theorem leb_trans : forall (n m p:nat),
    leb n m = true -> leb m p = true -> leb n p = true.
Proof.
    intros n m p Hnm Hmp. apply leb_correct. apply le_trans with (m:=m).
    - apply leb_complete. exact Hnm.
    - apply leb_complete. exact Hmp.
Qed.

Theorem leb_iff : forall (n m:nat),
    leb n m = true <-> n <= m.
Proof. 
    intros n m. split.
    - exact (leb_complete n m).
    - exact (leb_correct n m).
Qed.

Lemma le_n_0 : forall (n:nat), n <= 0 -> n = 0.
Proof. intros n H. inversion H. reflexivity. Qed.

Lemma not_le_Sm_n : forall (n m:nat), n <= m -> ~(S m <= n).
Proof.
  intros n m. revert n. induction m as [|m IH]. 
  - intros n H H'. apply le_n_0 in H. rewrite H in H'. inversion H'.
  - intros n H H'. remember (S m) as q eqn:H0. destruct H as [|p].
    + apply (IH n). 
      { apply Sn_le_Sm__n_le_m. rewrite <- H0. exact H'. }
      { apply le_n. }
    + apply (IH n). 
      { inversion H0 as [H2]. rewrite H2 in H. exact H. }
      { apply le_trans with (m:=S (S p)).
        { apply le_S, le_n. }
        { exact H'. }
      }
Qed.

Lemma not_le_Sn_n : forall (n:nat), ~(S n <= n).
Proof. intro n. apply not_le_Sm_n. apply le_n. Qed.


Theorem le_antisym : forall (n m:nat),
  n <= m -> m <= n -> n = m.
Proof.
  intros n m H. destruct H as [|p H].
  - intros _. reflexivity.
  - intros H'. exfalso. apply (not_le_Sn_n p).
    apply le_trans with (m:=n).
      + exact H'.
      + exact H.
Qed.


Theorem n_lt_m__Sn_lt_Sm : forall (n m:nat), n < m -> S n < S m.
Proof.
    intros n m H. unfold lt in H. unfold lt. apply n_le_m__Sn_le_Sm. exact H.
Qed.

Theorem Sn_lt_Sm__n_lt_m : forall (n m:nat), S n < S m -> n < m.
Proof.
    intros n m H. unfold lt in H. unfold lt. apply Sn_le_Sm__n_le_m. exact H.
Qed.

Theorem le_lt_dec : forall (n m:nat), {n <= m} + {m < n}. 
Proof.
    intros n. induction n as [|n IH].
    - left. apply le_0_n.
    - intros m. revert IH. revert n. induction m as [|m IH].
        + intros n _. right. unfold lt. apply n_le_m__Sn_le_Sm. apply le_0_n.
        + intros n H. destruct (H m) as [H'|H'].
            { left. apply n_le_m__Sn_le_Sm. exact H'. }
            { right. apply n_lt_m__Sn_lt_Sm. exact H'. }
Qed.


Lemma plus_le_compat_l : forall (n m p:nat),
    m <= p -> n + m <= n + p.
Proof.
    intros p. induction p as [|p IH].
    - intros m p H. exact H.
    - intros n m H. simpl. apply n_le_m__Sn_le_Sm. apply IH. exact H.
Qed.

Lemma plus_lt_compat_l : forall (n m p:nat),
    m < p -> n + m < n + p.
Proof.
    intros n m p H. unfold lt in H. unfold lt.
    rewrite <- plus_n_Sm. apply plus_le_compat_l. exact H.
Qed.

Theorem plus_le_compat : forall (n m n' m':nat),
    n <= n' -> m <= m' -> n + m <= n' + m'.
Proof.
    intros n m n' m' Hn Hm. apply le_trans with (m:=n + m').
    - apply plus_le_compat_l. exact Hm.
    - rewrite (plus_comm n m'), (plus_comm n' m'). apply plus_le_compat_l. exact Hn.
Qed.

Theorem plus_lt_compat : forall (n m n' m':nat),
    n < n' -> m < m' -> n + m < n' + m'.
Proof.
    intros n m n' m' Hn Hm. unfold lt in Hn. unfold lt in Hm. unfold lt.
    rewrite <- plus_n_Sm. apply le_trans with (m:=S n + S m).
    - rewrite (plus_comm n (S m)). rewrite (plus_comm (S n) (S m)).
        apply plus_le_compat_l. apply le_S, le_n.
    - apply plus_le_compat.
        + exact Hn.
        + exact Hm.
Qed.


Lemma sum_leq_sum : forall (n m p q:nat),
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
    intros n m p q H. 
    assert ({n <= p} + {p < n}) as [H0|H0]. {apply le_lt_dec. }
    - left. exact H0.
    - assert ({m <= q} + {q < m}) as [H1|H1]. {apply le_lt_dec. }
        + right. exact H1.
        + exfalso. assert (p + q < n + m) as H2. apply plus_lt_compat.
            { exact H0. } { exact H1. } 
            unfold lt in H2. assert ( S (p + q) <= p + q ) as H3.
            { apply le_trans with (m:=n+m). 
                { exact H2. }
                { exact H. } }
            apply (not_le_Sn_n (p + q)). exact H3.
Qed.
