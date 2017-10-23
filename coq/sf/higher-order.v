Require Import list.
Require Import bool.
Require Import nat.

Definition doit3times (a:Type) (f:a->a) (x:a) : a := f (f (f x)).

Arguments doit3times {a} _ _.

(*
Check @doit3times.
*)


Fixpoint filter (a:Type) (test: a -> bool) (l:list a) : list a :=
    match l with
    | []        => []
    | x::xs     => if test x then x::filter a test xs else filter a test xs
    end.


Arguments filter {a} _ _.


Example test_filter1 : filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition of_length_1 (a:Type) (l:list a) : bool := eqb (length l) 1.

Arguments of_length_1 {a} _.

Example test_filter2 : filter of_length_1 [[1,2],[3],[4],[5,6,7],[],[8]] =
    [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition countoddnumbers' (l:list nat) : nat := length (filter oddb l).

Example test_countoddnumbers'1 : countoddnumbers'[1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.


Example test_countoddnumbers'2 : countoddnumbers' [0,2,4] = 0.
Proof. reflexivity. Qed.

Example test_countoddnumbers'3 : countoddnumbers' [] = 0.
Proof. reflexivity. Qed.

Example test_anonymous_fun' : doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2' : filter (fun l => eqb (length l) 1)
    [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.








