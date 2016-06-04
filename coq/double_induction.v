Theorem nat_2_ind: forall P:nat->Prop,
  P 0 -> P 1 -> (forall n:nat, P n -> P (S n) -> P (S (S n))) -> forall n:nat, P n.
Proof.
  intros P H0 H1 IH n. cut (P n /\ P (S n)). tauto. elim n; intuition.
  (*
  clear n. split; assumption.
  clear n. intros n [H2 H3]. split. exact H3. apply IH. exact H2.
  *)
Qed.

Theorem nat_3_ind: forall P:nat->Prop,
  P 0 -> P 1 -> P 2 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n)) -> P (S (S (S n)))) ->
  forall n:nat, P n. 
Proof.
  intros P H0 H1 H2 IH n. 
  cut (P n /\ P (S n) /\ P (S (S n))). tauto. elim n; intuition.
Qed.
