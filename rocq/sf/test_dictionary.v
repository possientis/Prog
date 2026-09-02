Require Import bool.
Require Import nat.
Require Import dictionary.


Definition example_map1 : TotalMap bool :=
   t_update (t_update (t_empty false) (key 1) false) (key 3) true. 


Example test1 : example_map1 (key 0) = false.
Proof. reflexivity. Qed.


Example test2 : example_map1 (key 1) = false.
Proof. reflexivity. Qed.


Example test3 : example_map1 (key 2) = false.
Proof. reflexivity. Qed.


Example test4 : example_map1 (key 3) = true.
Proof. reflexivity. Qed.
