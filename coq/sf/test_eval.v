Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.

Example test_aeval0 : forall (env:State), aeval env (ANum 17) = 17.
Proof. reflexivity. Qed.


Example test_aeval1 : forall (env:State), aeval env (APlus (ANum 2) (ANum 5)) = 7.
Proof. reflexivity. Qed.


Example test_aeval2 : forall (env:State), aeval env (AMinus (ANum 12) (ANum 5)) = 7.
Proof. reflexivity. Qed.


Example test_aeval3 : forall (env:State), aeval env (AMult (ANum 4) (ANum 5)) = 20.
Proof. reflexivity. Qed.
