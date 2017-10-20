Require Import Arith.

Record Monoid (A:Type) : Type := monoid 
    {   identity_  : A
    ;   product_   : A -> A -> A
    ;   proof_idl   : forall x:A, product_ identity_ x = x
    ;   proof_idr   : forall x:A, product_ x identity_ = x
    ;   proof_asc   : forall x y z:A,
            product_ x (product_ y z) = 
            product_   (product_ x y) z 
    }
    .

(* redefining Monoid data with implicit type argument *)

Definition identity {A:Type} (m:Monoid A) : A := identity_ A m.
Definition product  {A:Type} (m:Monoid A) : A -> A -> A := product_ A m.


(* example of monoid *)

Definition Nat : Monoid nat := monoid nat
    0 
    plus plus_0_l 
    plus_0_r 
    plus_assoc
    .

Example identity_test : identity Nat = 0.
Proof. reflexivity. Qed. 

Example product_test : product Nat 3 4 = 7. 
Proof. reflexivity. Qed. 

(*
Check Nat.
Check identity Nat.
Check product Nat.
Check proof_idl nat Nat.
Check proof_idr nat Nat.
Check proof_asc nat Nat.
*)


