Require Import bool.
Require Import nat.
Require Import syntax.
Require Import state.


Fixpoint aeval (env:State) (a:aexp) : nat :=
    match a with
    | ANum n        => n
    | AKey k        => env k
    | APlus a1 a2   => (aeval env a1) + (aeval env a2)
    | AMinus a1 a2  => (aeval env a1) - (aeval env a2)
    | AMult a1 a2   => (aeval env a1) * (aeval env a2) 
    end.


Fixpoint beval (env:State) (b:bexp) : bool :=
    match b with
    | BTrue         => true
    | BFalse        => false
    | BEq a1 a2     => eqb (aeval env a1) (aeval env a2)
    | BLe a1 a2     => leb (aeval env a1) (aeval env a2)
    | BNot b1       => negb (beval env b1)
    | BAnd b1 b2    => andb (beval env b1) (beval env b2)
    end.


