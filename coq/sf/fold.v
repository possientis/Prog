Require Import list.
Require Import bool.

Fixpoint foldr (a b:Type) (f:a -> b -> b) (z:b) (l:list a) : b :=
    match l with
    | []        => z
    | x :: xs   => f x (foldr a b f z xs) 
    end.

Arguments foldr {a} {b} _ _ _.

(*
Check foldr andb.
*)

Example test_foldr1 : foldr mult 1 [1,2,3,4] = 24.
Proof. reflexivity. Qed.


Example test_foldr2 : foldr andb true [true,true,false,true] = false.
Proof. reflexivity. Qed.


Example test_foldr3 : foldr app [] [[1],[],[2,3],[4]] = [1,2,3,4].
Proof. reflexivity. Qed.

