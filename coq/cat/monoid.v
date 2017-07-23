Require Import Arith.

Record Monoid {A:Type} : Type := monoid 
    {   identity : A
    ;   product : A -> A -> A
    ;   proof_of_idl: forall x:A, product identity x = x
    ;   proof_of_idr: forall x:A, product x identity = x
    ;   proof_of_asc : forall x y z:A, 
            product x (product y z) = 
            product (product x y) z 
    }
    .

Definition natMonoid : Monoid := 
    monoid nat 0 plus plus_0_l plus_0_r plus_assoc.

Check natMonoid.
Check identity natMonoid.
Check product natMonoid.
Check proof_of_idl natMonoid.
Check proof_of_idr natMonoid.
Check proof_of_asc natMonoid.

