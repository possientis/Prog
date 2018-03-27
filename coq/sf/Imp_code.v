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

Definition subtract_slowly : com :=
    WHILE BNot (BEq (AKey x) (ANum 0)) DO
        Dec_x_z
    END.

Definition minus_5_4 : com :=
    x ::= ANum 3;;
    z ::= ANum 5;;
    subtract_slowly.

Definition loop : com :=
    WHILE BTrue DO
        SKIP
    END.

Definition pup_to_n : com :=
    y ::= ANum 0;;
    WHILE BNot (BEq (AKey x) (ANum 0)) DO
        y ::= APlus  (AKey y) (AKey x) ;;
        x ::= AMinus (AKey x) (ANum 1)
    END.


 

