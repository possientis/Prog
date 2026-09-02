Set Implicit Arguments.
Require Import ZArith.

Inductive htree (A:Set) : nat -> Set :=
  | hleaf : htree A 0
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Check htree_ind.
(*
forall (A : Set) (P : forall n : nat, htree A n -> Prop),
  P 0 (hleaf A) -> (forall (n : nat) (a : A) (left : htree A n), P n left -> forall right : htree A n, P n right -> P (S n) (hnode a left right)) 
  -> forall (n : nat) (h : htree A n), P n h
*)
Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.


Fixpoint htree_to_btree (n:nat)(t: htree Z n) : Z_btree :=
  match t with 
    | hleaf             => Z_leaf
    | hnode n v t1 t2   => Z_bnode v (htree_to_btree t1) (htree_to_btree t2)
  end.


Fixpoint invert (A:Set)(n:nat)(t: htree A n) : htree A n :=
  match t in htree _ x return htree A x with
    | hleaf             => hleaf A
    | hnode n v t1 t2   => hnode v (invert t2) (invert t1)
  end.


Definition left (n:nat)(t: htree nat n) := 
  match t in htree _ x return htree nat x with 
    | hleaf             =>  hleaf nat
    | hnode n v t1 t2   =>  t2
  end.

(*
Lemma injection: forall (n:nat)(t1 t2 t3 t4:htree nat n),
  hnode 0 t1 t2 = hnode 0 t3 t4 -> t1 = t3.
Proof.
  intros n t1 t2 t3 t4 H. discriminate H.
*)
