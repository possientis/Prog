Require Import Setoids.
Require Import Category7.

Record Functor (C D:Category) : Type := functor
    { Func          : Arr C -> Arr D
    ; Func_compat   : forall (f g:Arr C), f == g -> Func f == Func g
    }
    .
