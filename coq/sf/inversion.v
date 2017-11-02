Require Import list.

Theorem S_injective : forall (n m:nat),
    S n = S m -> n = m.
Proof.
    intros n m H. injection H. intros H'. exact H'.
Qed.

Theorem S_injective' : forall (n m:nat),
    S n = S m -> n = m.
Proof.
    intros n m H. inversion H as [H']. reflexivity.
Qed.


Theorem inversion_ex1 : forall (n m p:nat),
    [n,m] = [p,p] -> [n] = [m].
Proof.
    intros n m p H. inversion H. reflexivity.
Qed.

Theorem inversion_ex2: forall (n m:nat),
    [n] = [m] -> n = m.
Proof.
    intros n m H. inversion H as [H']. reflexivity.
Qed.

Theorem inversion_ex3: forall (a:Type) (x y z:a) (l k:list a),
    x :: y :: l = z :: k -> y :: l = x :: k -> x = y.
Proof.
    intros a x y z l k H1 H2. inversion H2. reflexivity.
Qed.




    


