Require Import nat.
Require Import dictionary.
Require Import state.
Require Import syntax.
Require Import equiv.


Definition prog_a : com :=
  WHILE BNot (BLe (AKey x) (ANum 0)) DO
    x ::= APlus (AKey x) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AKey x) (ANum 0) THEN
    x ::= APlus (AKey x) (ANum 1) ;;
    y ::= ANum 1
  ELSE
    y ::= ANum 0
  FI;;
  x ::= AMinus (AKey x) (ANum 1) ;;
  y ::= ANum 0.


