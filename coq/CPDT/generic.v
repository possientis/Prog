Require Import List.

Require Import vec.

Record Constructor : Type := Con 
    { Nonrecursive  : Type
    ; Recursive     : nat
    }
    .

Definition Datatype : Type := list Constructor.


Definition dtNil    : Datatype := nil.
Definition dtUnit   : Datatype := Con unit 0 :: nil.
Definition dtBool   : Datatype := Con unit 0 :: Con unit 0 :: nil.
Definition dtNat    : Datatype := Con unit 0 :: Con unit 1 :: nil.
Definition dtList (a:Type) : Datatype := Con unit 0 :: Con a 1 :: nil.

Inductive Tree (a:Type) : Type :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a
.

Arguments Leaf {a}.
Arguments Node {a}.

Definition dtTree (a:Type) : Datatype := Con a 0 :: Con unit 2 :: nil.


Definition constructorDenote (a:Type) (c:Constructor) : Type :=
    Nonrecursive c -> Vect a (Recursive c) -> a. 

