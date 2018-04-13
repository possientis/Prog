Require Import syntax.
Require Import eval.
Require Import state.


Definition aequiv (a1 a2:aexp) : Prop :=
  forall (e:State), aeval e a1 = aeval e a2.

Definition bequiv (b1 b2:bexp) : Prop :=
  forall (e:State), beval e b1 = beval e b2.

Definition cequiv (c1 c2:com)  : Prop :=
  forall (e e':State), ceval c1 e e' <-> ceval c2 e e'. 
