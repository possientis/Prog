Require Import bool.
Require Import nat.
Require Import syntax.


Fixpoint aeval (a:aexp) : nat :=
    match a with
    | ANum n        => n
    | APlus a1 a2   => (aeval a1) + (aeval a2)
    | AMinus a1 a2  => (aeval a1) - (aeval a2)
    | AMult a1 a2   => (aeval a1) * (aeval a2) 
    end.


Fixpoint beval (b:bexp) : bool :=
    match b with
    | BTrue         => true
    | BFalse        => false
    | BEq a1 a2     => eqb (aeval a1) (aeval a2)
    | BLe a1 a2     => leb (aeval a1) (aeval a2)
    | BNot b1       => negb (beval b1)
    | BAnd b1 b2    => andb (beval b1) (beval b2)
    end.
