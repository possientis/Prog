Require Import nat.
Require Import subst.
Require Import syntax.
Require Import state.


Example test_subst_aexp1 : 
    subst_aexp x (APlus (ANum 22) (ANum 13)) (APlus (AKey y) (AKey x)) =
    APlus (AKey y) (APlus (ANum 22) (ANum 13)).
Proof. reflexivity. Qed.

