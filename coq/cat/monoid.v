Require Import Arith.

Record Monoid (A:Type) : Type := monoid 
    {   identity  : A
    ;   product   : A -> A -> A
    ;   proof_idl : forall x:A, product identity x = x
    ;   proof_idr : forall x:A, product x identity = x
    ;   proof_asc : forall x y z:A,
            product x (product y z) = 
            product   (product x y) z 
    }
    .

(* implicit type argument *)
Arguments monoid    {A}.
Arguments identity  {A}.
Arguments product   {A}.
Arguments proof_idl {A}.
Arguments proof_idr {A}.
Arguments proof_asc {A}.


(* example of monoid *)

Definition Nat : Monoid nat := monoid 
    0           (* identity  *) 
    plus        (* product   *) 
    plus_0_l    (* proof_idl *) 
    plus_0_r    (* proof_idr *)
    plus_assoc  (* proof_asc *)
    .

(*
Check Nat.
Check identity  Nat.
Check product   Nat.
Check proof_idl Nat.
Check proof_idr Nat.
Check proof_asc Nat.
*)

Example identity_test : identity Nat = 0.
Proof. reflexivity. Qed. 

Example product_test : forall n m: nat, product Nat n m = n + m. 
Proof. reflexivity. Qed. 


