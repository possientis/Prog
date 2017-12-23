Axiom extensionality : forall (a b:Type) (f g: a -> b),
    (forall x, f x = g x) -> f = g.

Lemma extensionality2 : forall (a b c:Type) (f g: a -> b -> c),
    (forall x y, f x y = g x y) -> f = g.

Proof.
    intros a b c f g H. assert (forall x, f x = g x) as H'.
        { intros x. apply extensionality. apply (H x). }
        apply extensionality. exact H'.
Qed.

