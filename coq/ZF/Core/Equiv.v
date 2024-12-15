Require Import ZF.Core.Equal.

(* Types with equivalent classes                                                *)
Class Equiv (v:Type) (H:Equal v)
  := { EquivRefl : forall (x:v), x == x
     ; EquivSym  : forall (x y:v), x == y -> y == x
     ; EquivTran : forall (x y z:v), x == y -> y == z -> x == z
     }.

Arguments Equiv {v}.

(* Predicate expressing the fact a function is compatible with equivalences.    *)
Definition EquivCompat
  (v w:Type) (e:Equal v)(e':Equal w) (p:Equiv e) (p':Equiv e') (f:v -> w) : Prop :=
  forall (x y:v), x == y -> f x == f y.

Arguments EquivCompat {v} {w} {e} {e'} {p} {p'}.
