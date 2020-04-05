Definition NatE : forall (p:nat -> Prop), 
    p 0 -> (forall (n:nat), p n -> p (S n)) -> forall (n:nat), p n 
    := fix g(p:nat -> Prop)(H0:p 0)(IH:forall(m:nat),p m -> p (S m))(n:nat):p n 
    := match n with
       | 0     => H0
       | S m   => IH m (g p H0 IH m)
       end. 

Definition subst (a:Type) (p:a -> Prop) (x y:a) : x = y -> p x -> p y :=
    fun (e:x = y) (px:p x) =>
        match e with
        | eq_refl _ => px
        end.

Definition cong (a b:Type) (f:a -> b) (x y:a) : x = y -> f x = f y :=
    fun (e:x = y) =>
        subst a (fun (z:a) => f x = f z) x y e (eq_refl (f x)).

Definition L1 : forall (n:nat), n + 0 = n.
Proof.
refine ( fun(n:nat) => 
    NatE (fun (n:nat) => n + 0 = n) 
    (eq_refl 0) 
    (fun (m:nat) (H:m + 0 = m) => cong nat nat S (m + 0) m H)
    n
).
Qed.

