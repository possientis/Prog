Inductive Eq (a:Type) (x:a) : a -> Prop :=
| Eqrefl : Eq a x x
.

Arguments Eq {a}.

Arguments Eqrefl {a}.


Definition Eq_sym : forall (a:Type) (x y:a), Eq x y -> Eq y x :=
    fun (a:Type) =>
        fun (x y:a) =>
            fun (p:Eq x y) =>
                match p with
                | Eqrefl _ => Eqrefl _
                end.

Lemma Eq_refl' : forall (a:Type) (x y z:a),
    Eq x y -> Eq y z -> Eq x z.
Proof.
    intros a x y z H1 H2. destruct H1. assumption.
Qed.

    
