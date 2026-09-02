Require Import nat.
Require Import list.

Inductive eq (a:Type) : a -> a -> Prop := 
| eq_refl : forall (x:a), eq a x x
.

Arguments eq {a} _ _.
Arguments eq_refl {a} _.


Notation "x == y" := (eq x y) (at level 70, no associativity) : type_scope.


Lemma eq_reflexivity : forall (a:Type) (x:a), x == x.
Proof. intros a x. apply eq_refl. Qed.

Lemma eq_symmetry : forall (a:Type) (x y:a), x == y -> y == x.
Proof. intros a x y H. destruct H. apply eq_refl. Qed.

Lemma eq_transitivity : forall (a:Type) (x y z:a),
    x == y -> y == z -> x == z.
Proof. intros a x y z H. revert z. destruct H. intros z H. exact H. Qed.


Lemma leibniz_equality : forall (a:Type) (x y:a),
    x == y <-> forall (P:a -> Prop), P x -> P y.
Proof.
    intros a x y. split.
    - intros H. destruct H. intros P H. exact H.
    - intros H. apply H. apply eq_refl.
Qed.

Lemma four : 2 + 2 == 1 + 3.
Proof. apply eq_refl. Qed.


Definition four' : 2 + 2 == 1 + 3 := eq_refl 4.

Definition singleton : forall (a:Type) (x:a), [] ++ [x] == x :: [] :=
    fun (a:Type) (x:a) => eq_refl [x].

Definition quiz6 : exists x, x + 3 == 4 :=
    ex_intro (fun z => z + 3 == 4) 1 (eq_refl 4).


