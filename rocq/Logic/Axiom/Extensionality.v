Require Import Logic.Rel.R.

Axiom extensionality : forall (a b:Type) (f g: a -> b),
    (forall (x:a), f x = g x) -> f = g.

Axiom Ext : forall (a b:Type) (r s:R a b),
    (forall (x:a) (y:b), r x y <-> s x y) -> r = s.


