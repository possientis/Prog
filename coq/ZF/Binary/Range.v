Require Import ZF.Binary.
Require Import ZF.Class.

(* Range of a binary class.                                                    *)
Definition range (F:Binary) : Class := fun y => exists x, F x y.
