(* needed for second solution *)
Require Import Coq.Logic.JMeq.

Inductive test : Type :=
| make : forall (a:Type), a -> test
.

 
(* first solution: use a cast function *)

Definition cast (a b:Type) (p: a = b) (x:a) : b :=
    match p in _ = T return T with
    | eq_refl   => x
    end.

Arguments cast {a} {b} _ _.

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





