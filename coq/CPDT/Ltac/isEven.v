Inductive isEven : nat -> Prop :=
| Even_0  : isEven 0
| Even_SS : forall (n:nat), isEven n -> isEven (S (S n))
.

Ltac prove_even := repeat constructor.

Lemma L1 : isEven 256.
Proof. prove_even. Qed.

(*
Print L1.
*)

Lemma L2 : isEven 257.
Proof. prove_even. Abort.

Lemma L3 : 3 = 4.
Proof. prove_even. Abort.


