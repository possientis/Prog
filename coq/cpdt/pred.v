Extraction Language Haskell.

(*
Print Nat.pred.

Extraction Nat.pred.
*)

Lemma zltz : 0 < 0 -> False.
Proof. intros H. inversion H. Qed.

Definition pred_strong1 (n:nat) : (0 < n) -> nat :=
    match n with
    | 0     => (fun p => match zltz p with end)
    | S n   => (fun _           => n)
    end.

Arguments pred_strong1 {n} _.

Lemma zero_lt_one : 0 < 1.
Proof. constructor. Qed.


Lemma pred_strong1_test : pred_strong1 zero_lt_one = 0.
Proof. reflexivity. Qed.

