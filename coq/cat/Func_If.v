Require Import Func.

Definition ifRel (a b:Type) (p:Prop) (f g:a ==> b) (x:a) (y:b) :=
    (p /\ rel f x y) \/ (~p /\ rel g x y).


(* 
Definition Func_If (a b:Type) (P:Prop) (f g:a ==> b) :=
*)
