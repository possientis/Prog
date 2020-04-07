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

Definition z_not_s : forall (n:nat), 0 = S n -> False :=
    fun (n:nat) (e:0 = S n) =>
        subst nat (fun (m:nat) =>
            match m with
            | 0     => True
            | S _   => False
            end) 0 (S n) e I.

Definition sinj : forall (m n:nat), S m = S n -> m = n :=
    fun (m n:nat) (e:S m = S n) => 
        subst nat (fun (k:nat) =>
            match k with
            | 0     => True
            | S k   => m = k
            end) (S m) (S n) e (eq_refl m).


Definition L2 : forall (n:nat), S n = n -> False.
Proof.
refine ( NatE (fun (n:nat) => S n = n -> False) 
    (fun (e:1 = 0) => z_not_s 0 (eq_sym e))
    (fun (n:nat) (IH:S n = n -> False) (e:S (S n) = S n) => 
        IH (sinj (S n) n e)
)).
Qed.

Definition L3 : forall (n k:nat), n + S k = n -> False.
Proof.
refine ( NatE (fun (n:nat) => forall (k:nat), n + S k = n -> False)
    (fun (k:nat) (e:0 + S k = 0) => z_not_s k (eq_sym e))
    (fun (n:nat) (IH:forall (k:nat), n + S k = n -> False) =>
        fun (k:nat) (e:S n + S k = S n) => IH k (sinj (n + S k) n e) 
)).
Qed.

Definition L4 : forall (m n p:nat), m + n = m + p -> n = p.
Proof.
refine ( NatE (fun (m:nat) => forall (n p:nat), m + n = m + p -> n = p)
    (fun(n p:nat) (e:0 + n = 0 + p) => e)
    (fun(m:nat) (IH:forall (n p:nat), m + n = m + p -> n = p) =>
        fun (n p:nat) (e:S m + n = S m + p) => IH n p (sinj (m + n) (m + p) e)
)).
Qed.
