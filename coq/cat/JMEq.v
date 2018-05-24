(* needed for second solution *)
Require Import Coq.Logic.JMeq.
Require Import Cast.

Inductive test : Type :=
| make : forall (a:Type), a -> test
.


(* first solution: use a cast function *)


Lemma ex : forall (a b:Type) (x:a) (y:b) (p:a = b),
    cast p x = y -> make a x = make b y.
Proof.
    destruct p. intros p. simpl in p. rewrite p. reflexivity.
Qed.

(* second solution: heterogenous equality *)

Infix "==" := JMeq (at level 70, no associativity).

Lemma ex' : forall (a b:Type) (x:a) (y:b),
    a = b -> x == y -> make a x = make b y.
Proof.
    intros a b x y H0 H1. rewrite H1. reflexivity.
Qed.


Definition toOption (a b:Type) (p:a = b) : option a = option b.
Proof. rewrite p. reflexivity. Qed.

Arguments toOption {a} {b} _.



