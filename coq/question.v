Lemma L1 : forall (a b:Type) (p:a -> Prop) (q:a -> b -> Prop),
    (forall (x:a), p x -> exists (y:b), q x y) 
    <->
    (forall (x:a), exists (y:b), p x -> q x y).
Proof.
    intros a b p q. split; intros H x.
    -

Show.

