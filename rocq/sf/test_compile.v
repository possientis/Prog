Require Import nat.
Require Import list.
Require Import syntax.
Require Import state.
Require Import ISA.
Require Import compile.


Example test_compile1 : 
  s_compile (AMinus (AKey x) (AMult (ANum 2) (AKey y))) =
  [SLoad x, SPush 2, SLoad y, SMult, SMinus].
Proof. reflexivity. Qed.

