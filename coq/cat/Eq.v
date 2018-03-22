Record Eq (a:Type) : Type := equality 
    { eq    : a -> a -> Prop
    ; refl  : forall (x:a), eq x x
    ; sym   : forall (x y:a), eq x y -> eq y x
    ; trans : forall (x y z:a), eq x y -> eq y z -> eq x z
    }
    . 

Arguments eq {a} _ _ _.





