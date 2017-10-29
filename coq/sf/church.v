Definition nat : Type := forall (a:Type), (a -> a) -> a -> a.


Definition one : nat := fun (a:Type) (f:a -> a) (x:a) => f x.
Definition two : nat := fun (a:Type) (f:a -> a) (x:a) => f (f x).
Definition zero: nat := fun (a:Type) (f:a -> a) (x:a) => x.
Definition three:nat := fun (a:Type) (f:a -> a) (x:a) => f (f (f x)).
Definition four:nat := fun (a:Type) (f:a -> a) (x:a) => f (f (f (f x))).


Definition succ (n:nat) : nat := fun (a:Type) (f:a -> a) (x:a) => f (n a f x).   

Example test_succ1 : succ zero = one.
Proof. reflexivity. Qed.

Example test_succ2 : succ one = two.
Proof. reflexivity. Qed.

Example test_succ3 : succ two = three.
Proof. reflexivity. Qed.

Example test_succ4 : succ three = four.
Proof. reflexivity. Qed.

Definition plus (n m:nat) : nat :=
    fun (a:Type) (f:a -> a) (x:a) => n a f (m a f x).

Example test_plus1 : plus zero zero = zero.
Proof. reflexivity. Qed.

Example test_plus2 : plus one zero = one.
Proof. reflexivity. Qed.

Example test_plus3 : plus zero one = one.
Proof. reflexivity. Qed.

Example test_plus4 : plus one one = two.
Proof. reflexivity. Qed.

Example test_plus5 : plus two zero = two.
Proof. reflexivity. Qed.

Example test_plus6 : plus zero two = two.
Proof. reflexivity. Qed.

Example test_plus7 : plus one two = three.
Proof. reflexivity. Qed.

Example test_plus8 : plus two one = three.
Proof. reflexivity. Qed.


Definition mult (n m:nat) : nat :=
    fun (a:Type) (f:a -> a) (x:a) => n a (m a f) x.

Example test_mult1 : mult zero zero = zero.
Proof. reflexivity. Qed.

Example test_mult2 : mult one zero = zero.
Proof. reflexivity. Qed.

Example test_mult3 : mult zero one = zero.
Proof. reflexivity. Qed.

Example test_mult4 : mult one one = one.
Proof. reflexivity. Qed.

Example test_mult5 : mult two zero = zero.
Proof. reflexivity. Qed.

Example test_mult6 : mult zero two = zero.
Proof. reflexivity. Qed.

Example test_mult7 : mult one two = two.
Proof. reflexivity. Qed.

Example test_mult8 : mult two one = two.
Proof. reflexivity. Qed.

Example test_mult9 : mult two two = four.
Proof. reflexivity. Qed.

Example test_mult10 : mult two three = plus three three.
Proof. reflexivity. Qed.


Definition exp (n m: nat) : nat :=
 fun (a:Type) (f:a -> a) (x:a) => 
