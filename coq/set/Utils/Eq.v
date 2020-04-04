Class Eq (a:Type) :=
    { eqDec : forall (x y:a), { x = y }   + { ~ x = y }
    }.

