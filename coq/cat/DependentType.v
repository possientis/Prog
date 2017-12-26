Inductive test : Type :=
| make : forall (a:Type), a -> test
.

Definition x:test := make nat 0.
Definition y:test := make nat 0.

Example eq_x_y : x = y.
Proof. reflexivity. Qed.


Definition f (n:nat) : test := make nat n.
Definition g (n:nat) : test := make nat n.

Example eq_fn_fm : forall (n m:nat),
    n = m -> f n = f m.
Proof. intros n m H. rewrite H. reflexivity. Qed.


Definition make' (a:Type) : a -> test :=
    fun x => make a x.

