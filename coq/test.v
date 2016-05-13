Lemma lem : (forall n0 : nat, 0 <= n0 -> 0 <= S n0) -> forall n, le 0 n.
Proof.
  intros H n.
