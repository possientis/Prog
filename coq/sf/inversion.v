Require Import list.
Require Import nat.
Require Import bool.

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

Theorem inversion_ex2 : forall (n m:nat),
    [n] = [m] -> n = m.
Proof.
    intros n m H. inversion H as [H']. reflexivity.
Qed.

Theorem inversion_ex3 : forall (a:Type) (x y z:a) (l k:list a),
    x :: y :: l = z :: k -> y :: l = x :: k -> x = y.
Proof.
    intros a x y z l k H1 H2. inversion H2. reflexivity.
Qed.


Theorem f_equal : forall (a b:Type) (f:a -> b) (x y:a),
    x = y -> f x = f y.
Proof. intros a b f x y H. rewrite H. reflexivity. Qed.

Theorem eqb_nat_0_l : forall n:nat, eqb 0 n = true -> n = 0.
Proof.
    intros n. destruct n as [|n].
    - intros. reflexivity.
    - simpl. intros H. inversion H.
Qed.

Theorem inversion_ex4 : forall (n:nat), S n = 0 -> 2 + 2 = 5.
Proof. intros n H. inversion H. Qed.

Theorem inversion_ex5 : forall (n m:nat), 
    false = true -> [n] = [m].
Proof. intros n m H. inversion H. Qed.

Theorem inversion_ex6 : forall (a:Type) (x y z:a) (l k:list a),
    x :: y :: l = [] -> y :: l = z :: k -> x = z.
Proof. intros a x y z l k H1 H2. inversion H1. Qed.



    


