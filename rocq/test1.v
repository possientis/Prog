Lemma L1 : forall (n m:nat) (p:nat -> Prop), 
    (p n /\ exists (u:nat), p u /\ p m) \/ (~p n /\ p m) -> n = m.
Proof.
    intros n m p [[H1 [u [H2 H3]]]|[H1 H2]].
    - admit.
    -
Show.
