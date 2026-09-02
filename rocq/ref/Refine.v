Lemma L1 : forall (n:nat), n + 0 = n.
Proof.
    refine (fun (n:nat) =>
        match n with
        | 0     => eq_refl _
        | S n   => _
        end).

Show.
