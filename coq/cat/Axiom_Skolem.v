Axiom Skolem : forall (a:Type) (P:a -> Prop),
    (exists x, P x) ->
    (forall x y, P x -> P y -> x = y) -> {x:a | P x}. 
