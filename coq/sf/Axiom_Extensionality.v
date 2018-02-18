Axiom extensionality : forall (a:Type) (b:a -> Type) (f g:forall x, b x),
    (forall x, f x = g x) -> f = g.

