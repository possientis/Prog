Require Import nat.
Require Import list.
Require Import dictionary.
Require Import state.
Require Import compile.
Require Import execute.



Example test_execute1 : s_execute emptyState []
  [SPush 5, SPush 3, SPush 1, SMinus] = [2,5].
Proof. reflexivity. Qed.

Example test_execute2 : s_execute (t_update emptyState x 3) [3,4]
  [SPush 4, SLoad x, SMult, SPlus] = [15,4].
Proof. reflexivity. Qed.


