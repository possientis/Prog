Require Import nat.
Require Import syntax.

Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with 
    | ANum n                => ANum n
    | APlus (ANum 0) a2     => optimize_0plus a2
    | APlus a1 a2           => APlus  (optimize_0plus a1) (optimize_0plus a2)
    | AMinus a1 a2          => AMinus (optimize_0plus a1) (optimize_0plus a2)
    | AMult a1 a2           => AMult  (optimize_0plus a1) (optimize_0plus a2)
    end.
