Require Import Logic.Set.Set.

Require Import Logic.Class.Ord.

Require Import Logic.Set.Normal.Leq.

Global Instance ordSet : Ord set :=
    { leq      := leq
    ; leqDec   := leqDec
    ; leqRefl  := leqRefl
    ; leqTrans := leqTrans
    ; leqAsym  := leqASym
    ; leqTotal := leqTotal
    }. 
