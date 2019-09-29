Fixpoint blt_nat (n m:nat) : bool :=
    match n with
    | 0 => 
        match m with
        | 0     => false
        | S _   => true
        end
    | S n'  =>
        match m with
        | 0     => false
        | S m'  => blt_nat n' m'
        end
    end.

Lemma nat_dec : forall (n m:nat), {n = m} + {n <> m}.
Proof.
    induction n as [|n IH].
    - destruct m as [|m].
        + left. reflexivity.
        + right. intros H. inversion H.
    - destruct m as [|m].
        + right. intros H. inversion H.
        + destruct (IH m) as [H|H].
            { left. rewrite H. reflexivity. }
            { right. intros H'. apply H. inversion H'. reflexivity. }
Qed.

