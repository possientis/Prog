Require Import nat.

Definition square (n:nat) : nat := n * n.

Lemma square_mult : forall (n m:nat), 
    square (n * m) = square n * square m.
Proof.
    intros n m. unfold square.
    assert ((n * m) * (n * m) = ((n * m) * n) * m) as H1.
        { rewrite <- mult_assoc. reflexivity. }
    assert (((n * m) * n) * m = (n * (m * n)) * m) as H2.
        { rewrite (mult_assoc n m n). reflexivity. } 
    assert ((n * (m * n)) * m = n * (n * m) * m) as H3.
        { rewrite (mult_comm m n). reflexivity. }
    assert (n * (n * m) * m = ((n * n) * m) * m) as H4.
        { rewrite <- (mult_assoc n n m). reflexivity. }
    assert (((n * n) * m) * m = (n * n) * (m * m)) as H5.
        { rewrite (mult_assoc (n * n) m m).  reflexivity. }
    rewrite H1, H2, H3, H4, H5. reflexivity.
Qed.


