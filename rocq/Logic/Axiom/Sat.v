Definition tsat (f:nat -> bool) : Prop := exists (n:nat), f n = true.

Lemma tsatOr : forall (f g:nat -> bool), 
    (tsat f \/ tsat g) -> tsat (fun n => orb (f n) (g n)).
Proof.
    intros f g [H1|H1]; destruct H1 as [n H1]; exists n; rewrite H1.
    - destruct (g n); reflexivity.
    - destruct (f n); reflexivity.
Qed.
