Require Import List.

Require Import Eq.

Require Import Lam.T.
Require Import Lam.Free.
Require Import Lam.Subformula.

Definition valid (v w:Type) (e:Eq v) (e':Eq w) (f:v -> w) (t:T v) : Prop :=
    forall (s:T v) (x:v), s <<= t -> 
        In x (free e s) -> In (f x) (free e' (fmap f s)).
