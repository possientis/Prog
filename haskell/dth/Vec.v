(*
Require Import Arith_base.
Require Import Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.
*)


Inductive Vec (a:Type) : nat -> Type :=
| nil  : Vec a 0
| cons : forall (x:a) (n:nat), Vec a n -> Vec a (S n)
.

(*
Check Vec.
Check nil.
Check cons.
*)


