Require Import Category6.

Record Functor (C D:Category) : Type := functor
    { F0 : Obj C -> Obj D
    ; F1 : forall (a b:Obj C), Hom a b -> Hom (F0 a) (F0 b)
    }
    .
