Record IsMonoid (a:Type) (r : a -> a -> a) (e:a) : Prop :=
    { assoc : forall (x y z:a), r (r x y) z = r x (r y z)
    ; identity_l : forall (x:a), r e x = x
    ; identity_r : forall (x:a), r x e = x    
    }.
