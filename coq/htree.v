Set Implicit Arguments.

Inductive htree (A:Set) : nat -> Set :=
  | hleaf : htree A 0
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Check htree_ind.
(*
forall (A : Set) (P : forall n : nat, htree A n -> Prop),
  P 0 (hleaf A) -> (forall (n : nat) (a : A) (left : htree A n), P n left -> forall right : htree A n, P n right -> P (S n) (hnode a left right)) 
  -> forall (n : nat) (h : htree A n), P n h
*)

