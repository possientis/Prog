
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
Arguments monoid    {A} _ _ _ _ _.
Arguments identity  {A} _.
Arguments product   {A} _ _ _.
Arguments proof_idl {A} _ _.
Arguments proof_idr {A} _ _.
Arguments proof_asc {A} _ _ _ _.




