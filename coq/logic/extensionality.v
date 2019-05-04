Axiom extensionality : forall (a b:Type) (f g: a -> b),
    (forall (x:a), f x = g x) -> f = g.

