Theorem lt_le: forall n p: nat, n < p -> n <= p.
Proof.
(*
  intros  n p H. unfold lt in H. apply le_S_n. apply le_S. exact H.
Qed.
*)
 
