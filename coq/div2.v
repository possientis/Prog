Require Import Arith.

Fixpoint div2 (n:nat) : nat :=
  match n with
    | 0       => 0
    | 1       => 0
    | S (S p) => S (div2 p)
  end.


Lemma div2_le' : forall (n k:nat),
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


Theorem div2_le: forall (n:nat), div2 n <= n.
Proof.
  intros n. apply div2_le' with (n:=n). auto.  
Qed.
