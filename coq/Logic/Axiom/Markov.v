Require Import Logic.Axiom.Sat.

Definition Markov : Prop := forall (f:nat -> bool),
    ~(forall n, f n = false) -> tsat f.
