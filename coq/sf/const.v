Require Import higher_order.

Definition constfun (a:Type) (x:a) : nat -> a :=
        fun (k:nat) => x.

Arguments constfun {a} _ _.

Definition ftrue := constfun true.


Example test_constfun1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example test_constfun2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(*
Check plus.
*)

Definition plus3 := plus 3.

(*
Check plus3.
*)

Example test_plus3_1 : plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3_2 : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.


Example test_plus3_3 : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.
