(*
Require Import Category6.
Require Import Setoids.

Definition setoidsAsCategory : Category := category 
    Setoid 
    Map
    (@compose) 
    id 
    MapEq
    id_left 
    id_right
    compose_assoc
    composition_is_compat.
*)
