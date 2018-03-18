Require Category5.
Module Cat := Category5.
Require Import Setoids.

Definition compose'(a b c:Setoid)(f:Hom a b)(g:Hom b c):Hom a c := g @ f.

Definition SetoidsAsCategory5 : Cat.Category5 := Cat.category5
    Setoid
    Hom
    compose'
    id
    id_left
    id_right
    compose_assoc.


