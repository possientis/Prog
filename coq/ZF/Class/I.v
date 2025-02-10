Require Import ZF.Class.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The class of all ordered pairs of the form (x,x).                            *)
Definition I : Class := fun x => exists y, x = :(y,y):.
