Inductive SNat : nat -> Type :=
| SZ : SNat 0
| SS : forall (n:nat), SNat n -> SNat (S n)
.

Arguments SS {n}.

Fixpoint inj (n:nat) : SNat n :=
    match n with
    | 0     => SZ
    | S n   => SS (inj n)
    end.


Definition f n : SNat n := inj n.

Definition g : forall (n:nat), SNat n := fun n => inj n.

