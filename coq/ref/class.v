Class EqDec (a : Type) :=
    { eqb : a -> a -> bool
    ; eqb_leibniz : forall x y, eqb x y = true -> x = y
    }.
