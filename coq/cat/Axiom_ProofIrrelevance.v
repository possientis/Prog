Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

Axiom test_prop : forall (P Q: Prop), (P <-> Q) -> P = Q.
