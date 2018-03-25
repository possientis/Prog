Require Import nat.
Require Import syntax.
Require Import state.

Definition fact_in_coq : com :=
    z ::= AKey x;; 
    y ::= ANum 1;;
    WHILE BNot (BEq (AKey z) (ANum 0)) DO
        y ::= AMult (AKey y) (AKey z);;
        z ::= AMinus (AKey z) (ANum 1)
    END.


Definition Add2_x : com := x ::= (APlus (AKey x) (ANum 2)).

Definition Mult_x_y_z : com := z::= AMult (AKey x) (AKey y).

Definition Dec_x_z : com := 
    z ::= AMinus (AKey z) (ANum 1);;
    x ::= AMinus (AKey x) (ANum 1).




 

