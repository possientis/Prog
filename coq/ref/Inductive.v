Inductive Foo : Set :=
| A : Foo
| B : nat -> Foo
| C : Foo -> Foo
.

Check Foo_ind.
Check Foo_rec.


Fixpoint Foo_rect' 
    (P:Foo -> Type) 
    (pa:P A)
    (pb:forall (n:nat), P (B n))
    (pc: forall (f:Foo), P f -> P (C f)) (f:Foo): P f
    :=
    match f with
    | A     => pa
    | B n   => pb n
    | C f'  => pc f' (Foo_rect' P pa pb pc f')
    end.

Check Foo_rect.
Check Foo_rect'.
