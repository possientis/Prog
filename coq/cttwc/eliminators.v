
Definition BoolE : forall (p:bool -> Prop), p true -> p false -> forall (x:bool), p x :=
    fun (p:bool -> Prop) => 
        fun (tt:p true) =>
            fun (ff: p false) =>
                fun (x:bool) =>
                    match x with
                    | true  => tt
                    | false => ff
                    end.

Definition BoolC1 : bool := true.
Definition BoolC2 : bool := false.

Definition L1 : forall (x:bool), negb (negb x) = x.
Proof.
    intros x.
    apply (BoolE (fun z => negb (negb z) = z)).
    - exact (eq_refl true).
    - exact (eq_refl false).
Qed.


Definition L2 : forall (x:bool), negb (negb x) = x :=
    fun (x:bool) => BoolE 
        (fun (z:bool) => negb (negb z) = z) 
        (eq_refl true) 
        (eq_refl false) 
        x.
