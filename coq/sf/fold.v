Require Import nat.
Require Import bool.
Require Import list.
Require Import fmap.

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


Definition fold_length (a:Type) (l:list a) : nat :=
    foldr (fun _ n => S n) 0 l.

Arguments fold_length {a} _.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Example test_fold_length2 : fold_length ([]:list nat) = 0.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall (a:Type) (l:list a),
    fold_length l = length l.
Proof.
    induction l as [| x xs H].
    - reflexivity.
    - unfold fold_length. simpl. fold (fold_length xs). rewrite H. reflexivity.
Qed.


Definition fold_map (a b:Type) (f:a -> b) (l:list a) : list b :=
    foldr (fun x ys => f x :: ys) [] l.

Arguments fold_map {a} {b} _ _.

Example fold_map_test1 : fold_map (fun n => n * n) [] = [].
Proof. reflexivity. Qed.


Example fold_map_test2 : fold_map (fun n => n * n) [1,2,3] = [1,4,9].
Proof. reflexivity. Qed.

Theorem fold_map_correct : forall (a b:Type) (f:a -> b) (l:list a),
    fold_map f l = map f l.
Proof.
    induction l as [|x xs H].
    - reflexivity.
    - unfold fold_map. simpl. fold (fold_map f xs). rewrite H. reflexivity.
Qed.





