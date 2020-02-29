(* Leibniz symmetry                                                             *)
Definition L1 : forall (a:Type) (x y:a),
    (forall (p:a -> Prop), p x -> p y) -> (forall (p:a -> Prop), p y -> p x) :=
    fun (a:Type) =>
        fun(x y:a) =>
            fun (f: forall (p:a -> Prop), p x -> p y) =>
                fun (p:a -> Prop) => 
                    f (fun (z:a) => (p z -> p x)) (fun k => k).



Definition L2 : forall (a:Type) (x y:a),
    (forall (p:a -> Prop), p x -> p y) -> (forall (p:a -> Prop), p y -> p x).
Proof.
    intros a x y f p. 
    change ((fun z => p z -> p x) y).
    apply f.
    exact (fun z => z).
Qed.
