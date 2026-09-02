Require Import Arith.
Require Import Monoid.
Import Nat.

(* a monoid can be defined from nat 0 and plus *)
Definition NatPlus : Monoid nat := monoid 
    0          (* identity  *) 
    plus       (* product   *) 
    add_0_l    (* proof_idl *) 
    add_0_r    (* proof_idr *)
    add_assoc  (* proof_asc *)
    .

(* a monoid can be defined from nat 1 and mult *)
Definition NatMult : Monoid nat := monoid
    1
    mult
    mul_1_l
    mul_1_r
    mul_assoc
    .

(*
Check NatPlus.
Check identity  NatPlus.
Check product   NatPlus.
Check proof_idl NatPlus.
Check proof_idr NatPlus.
Check proof_asc NatPlus.

Check NatMult.
Check identity  NatMult.
Check product   NatMult.
Check proof_idl NatMult.
Check proof_idr NatMult.
Check proof_asc NatMult.
*)

Example plus_identity_test : identity NatPlus = 0.
Proof. reflexivity. Qed. 

Example plus_product_test : forall n m: nat, product NatPlus n m = n + m. 
Proof. reflexivity. Qed. 

Example mult_identity_test : identity NatMult = 1.
Proof. reflexivity. Qed. 

Example mult_product_test : forall n m: nat, product NatMult n m = n * m. 
Proof. reflexivity. Qed. 


