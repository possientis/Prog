Require Import Logic.Rel.R.
Require Import Logic.Rel.Total.
Require Import Logic.Rel.Functional.

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

Definition Function (a b:Type) (r:R a b) : Prop := Functional r /\ Total r.

Arguments Function {a} {b}.

Lemma funcIsFunction : forall (a b:Type) (f:a -> b), Function (func f).
Proof.
    intros a b f. split.
    - apply Functional_charac. intros x y y' H1 H2. destruct H1, H2. reflexivity.
    - apply Total_charac. intros x. exists (f x). constructor.
Qed.


