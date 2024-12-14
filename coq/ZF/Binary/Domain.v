Require Import ZF.Binary.
Require Import ZF.Class.

(* Domain of a binary class.                                                    *)
Definition domain (F:Binary) : Class := fun x => exists y, F x y.
