Axiom extensionality : forall (a:Type) (B:a -> Type) (f g: forall x:a, B x),
    (forall x, f x = g x) -> f = g.

Lemma extensionality2 : forall(a b:Type) (B:a -> b -> Type) (f g:forall x y,B x y),
    (forall x y, f x y = g x y) -> f = g.
Proof.
    intros a b B f g H.
    apply extensionality. intros x.
    apply extensionality. intros y.
    apply H.
Qed.

Lemma extensionality3: forall (a b c:Type) (B:a -> b -> c-> Type)
    (f g:forall x y z, B x y z),
    (forall x y z, f x y z = g x y z) -> f = g.
Proof.
    intros a b c B f g H.
    apply extensionality. intros x.
    apply extensionality. intros y.
    apply extensionality. intros z.
    apply H.
Qed.




