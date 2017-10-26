Require Import nat.
Require Import bool.
Require Import natoption.

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

Inductive natdict : Type :=
    | empty : natdict
    | record : key -> nat -> natdict -> natdict
    .


Definition update (d: natdict) (k: key) (n:nat) : natdict :=
    record k n d.

Fixpoint find (k:key) (d: natdict) : natoption := 
    match d with
    | empty     => None
    | record k' n d'    => if eqb_key k k'
        then Some n
        else find k d'
    end.
       
Theorem update_eq : forall (d:natdict) (k:key) (n:nat),
    find k (update d k n) = Some n.
Proof. intros d k n. simpl. rewrite eqb_key_refl. reflexivity. Qed.

Theorem eqb_key_semantics : forall k l:key,
    k = l <-> eqb_key k l= true.
Proof.
    intros k l. split.
    - intros H. rewrite H. apply eqb_key_refl.
    - destruct k as [n]. destruct l as [m]. simpl. intros H.
      assert (n = m) as H'. { apply eqb_semantics. exact H. }
      rewrite H'. reflexivity.
Qed.

Theorem update_neq : forall (d:natdict) (k l:key) (n:nat),
    eqb_key k l = false -> find k (update d l n) = find k d.
Proof. intros d k l n H. simpl. rewrite H. reflexivity. Qed.


