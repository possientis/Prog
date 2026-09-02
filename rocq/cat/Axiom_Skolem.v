Axiom skolem : forall (a:Type) (P:a -> Prop),
    (exists x, P x) ->
    (forall x y, P x -> P y -> x = y) -> {x:a | P x}. 

Arguments skolem {a} _ _ _.
