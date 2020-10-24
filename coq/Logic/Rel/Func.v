Require Import Logic.Rel.R.

Inductive func (a b:Type) (f:a -> b) : R a b :=
| mkFunc : forall (x:a), func a b f x (f x)
.

Arguments func {a} {b}.

Lemma func_charac : forall (a b:Type) (f:a -> b) (x:a) (y:b),
    func f x y <-> f x = y.
Proof.
    intros a b f x y. split; intros H1. 
    - destruct H1. reflexivity.
    - rewrite <- H1. constructor.
Qed.



