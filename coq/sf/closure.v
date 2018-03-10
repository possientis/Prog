Require Import nat.
Require Import le.

Definition relation (a:Type) : Type := a -> a -> Prop.

Inductive clos (a:Type) (r:relation a) : relation a :=
| rt_step : forall x y, r x y -> clos a r x y
| rt_refl : forall x, clos a r x x
| rt_trans: forall x y z, clos a r x y -> clos a r y z -> clos a r x z
.

Arguments clos {a} _.

Inductive next : relation nat := nextS : forall n, next n (S n).


Lemma le_is_clos_next : forall (n m:nat), n <= m <-> clos next n m.
Proof.
    intros n m . split.
    - intros H.

Show.


