Definition pierce := forall (p q : Prop), ((p -> q) -> p) -> p.
Definition lem := forall (p : Prop), p \/ ~p.

Theorem pierce_lem_equiv : pierce <-> lem.
Proof.
  unfold pierce, lem.
  firstorder.
  apply H with (q := ~(p \/ ~p)).
  firstorder.
