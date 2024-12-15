Require Import ZF.Core.Equal.

(* Types with equivalent classes                                                *)
Class Equiv (v:Type) (H:Equal v)
  := { EquivRefl : forall (x:v), x == x
     ; EquivSym  : forall (x y:v), x == y -> y == x
     ; EquivTran : forall (x y z:v), x == y -> y == z -> x == z
     }.

Arguments Equiv _ {H}.
