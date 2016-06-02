Require Import Arith.

Fixpoint div2 (n:nat) : nat :=
  match n with
    | 0       => 0
    | 1       => 0
    | S (S p) => S (div2 p)
  end.


Lemma div2_le_lem : forall (n k:nat),
  k <= n -> div2 k <= k.
Proof.
  intros n. elim n.
  clear n.  intros k. elim k.
  clear k. simpl. auto.
  clear k. intros k H0 H1. apply le_n_0_eq in H1. discriminate.
  clear n. intros n IH k. elim k.
  clear k. simpl. auto.
  clear k. intros k.  elim k.
  clear k. simpl. auto.
  clear k. intros k H0 H1 H2. simpl. apply le_n_S.
  apply le_trans with (m:=k). apply IH.
  apply le_S_n. apply le_trans with (m:= S (S k)). apply le_n_S. auto.
  exact H2. auto.
Qed.


Theorem div2_le': forall (n:nat), div2 n <= n.
Proof.
  intros n. apply div2_le_lem with (n:=n). auto.  
Qed.


Theorem div2_le : forall (n:nat), div2 n <= n.
Proof.
  intros n. cut (div2 n <= n /\ div2 (S n) <= S n). tauto.
  elim n. simpl. auto.
  clear n. intros n [H1 H2]. (* tick to split conjunction immediately *)
  split. exact H2. simpl. auto with arith.
Qed.


Fixpoint div3 (n:nat) : nat :=
  match n with
    | 0           => 0
    | 1           => 0
    | 2           => 0
    | S (S (S p)) => S (div3 p) 
  end.

Theorem div3_le : forall (n:nat), div3 n <= n.
Proof.
  intros n.
  cut (div3 n <= n /\ div3 (S n) <= S n /\ div3 (S (S n)) <= S (S n)). tauto.
  elim n. simpl. auto.
  clear n. intros n [H0 [H1 H2]]. (* even bigger trick *)
  split. exact H1. split. exact H2. simpl. auto with arith.
Qed.


Fixpoint mod2 (n:nat) : nat :=
  match n with
    | 0       => 0
    | 1       => 1
    | S (S p) => mod2 p
  end.

Theorem eucl2 : forall (n:nat),
  n = 2 * (div2 n) + mod2 n.
Proof.
  intro n.
  cut (n = 2 * (div2 n) + mod2 n /\ S n = 2 * (div2 (S n)) + mod2 (S n)). tauto.
  elim n. simpl. auto.
  clear n. intros n [H0 H1]. (* trick *)
  split.  exact H1. simpl. rewrite plus_0_r.
  cut (S n = div2 n + S (div2 n) + mod2 n). eauto.
  rewrite H0 at 1. simpl. rewrite plus_0_r. simpl. 
  rewrite <- plus_n_Sm.
  rewrite plus_Snm_nSm.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.





