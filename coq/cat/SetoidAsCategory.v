Require Import Category6.
(*Module Cat := Category5.*)
Require Setoids.
Module S := Setoids.

Definition SetoidAsCategory : Category := category
    S.Setoid
    S.Hom
    @S.compose
    S.id
    S.id_left
    S.id_right
    S.compose_assoc.

