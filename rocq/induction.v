Lemma L1 : forall (n:nat), n + 0 = n.
Proof.
  intro n. elim n. simpl. reflexivity.
  clear n. intros n IH. simpl. rewrite IH. reflexivity.
Qed.

(* same, but using induction and auto tactic *)

Lemma L2 : forall (n:nat), n + 0 = n.
Proof.
  induction n; auto.
Qed.


