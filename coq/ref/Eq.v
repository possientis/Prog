Inductive Eq (a:Type) (x:a) : a -> Prop :=
| Eq_refl : Eq a x x
.

Arguments Eq {a}.

Arguments Eq_refl {a}.


Definition Eq_sym : forall (a:Type) (x y:a), Eq x y -> Eq y x :=
    fun (a:Type) =>
        fun (x y:a) =>
            fun (p:Eq x y) =>
                match p with
                | Eq_refl _ => Eq_refl _
                end.


    
