Require Import nat.
Require Import bool.

Inductive key : Type :=
    | Key : nat -> key
    .

Definition eqb_key k1 k2 : bool :=
    match k1,k2 with
        | Key n1, Key n2    => eqb n1 n2
    end.

Example eqb_key1 : eqb_key (Key 23) (Key 23) = true.
Proof. reflexivity. Qed.


Example eqb_key2 : eqb_key (Key 23) (Key 24) = false.
Proof. reflexivity. Qed.

Theorem eqb_key_refl : forall k:key, eqb_key k k = true.
Proof.
    destruct k as [n]. simpl. apply eqb_refl.
Qed.

Inductive partial_map : Type :=
    | empty : partial_map
    | record : key -> nat -> partial_map -> partial_map
    .

