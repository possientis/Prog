Require Import nat.
Require Import syntax.

Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with 
    | ANum n                => ANum n
    | AKey k                => AKey k
    | APlus (ANum 0) a2     => optimize_0plus a2
    | APlus a1 a2           => APlus  (optimize_0plus a1) (optimize_0plus a2)
    | AMinus a1 a2          => AMinus (optimize_0plus a1) (optimize_0plus a2)
    | AMult a1 a2           => AMult  (optimize_0plus a1) (optimize_0plus a2)
    end.


Fixpoint optimize_0plus_b (b:bexp) : bexp :=
    match b with
    | BTrue                 => BTrue
    | BFalse                => BFalse
    | BEq a1 a2             => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2             => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1               => BNot (optimize_0plus_b b1)
    | BAnd b1 b2            => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.
