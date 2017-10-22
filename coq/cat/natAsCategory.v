Require Import Category.
Require Import natAsMonoid.
Require Import MonoidAsCategory.

(* turning the monoids NatPlus and NatMult into a categories *)

Definition NatPlusAsCat : Category nat := toCategory NatPlus.
Definition NatMultAsCat : Category nat := toCategory NatMult.

(*
Check NatPlusAsCat.
Check NatMultAsCat.
*)

(* the source of every morphism is the identity of the monoid *)

Example source_test1 : forall n:nat, source NatPlusAsCat n = 0.
Proof. reflexivity. Qed.

Example source_test2 : forall n:nat, source NatMultAsCat n = 1.
Proof. reflexivity. Qed.



(* the target of every morphism is the identity of the monoid *)

Example target_test1 : forall n:nat, target NatPlusAsCat n = 0.
Proof. reflexivity. Qed.

Example target_test2 : forall n:nat, target NatMultAsCat n = 1.
Proof. reflexivity. Qed.



(* composition is defined everywhere and coincides with summation *)

Example compose_test1 : forall n m:nat, compose NatPlusAsCat n m = Some (n + m).
Proof. reflexivity. Qed.


Example compose_test2 : forall n m:nat, compose NatMultAsCat n m = Some (n * m).
Proof. reflexivity. Qed.


