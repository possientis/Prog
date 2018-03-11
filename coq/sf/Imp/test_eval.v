Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.

Example test_aeval0 : aeval (ANum 17) = 17.
Proof. reflexivity. Qed.


Example test_aeval1 : aeval (APlus (ANum 2) (ANum 5)) = 7.
Proof. reflexivity. Qed.


Example test_aeval2 : aeval (AMinus (ANum 12) (ANum 5)) = 7.
Proof. reflexivity. Qed.


Example test_aeval3 : aeval (AMult (ANum 4) (ANum 5)) = 20.
Proof. reflexivity. Qed.
