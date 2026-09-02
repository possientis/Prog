Require Import Logic.Rel.R.
Require Import Logic.Rel.Total.
Require Import Logic.Rel.Function.
Require Import Logic.Rel.Functional.

Inductive embed (a b:Type) (f:a -> b) : R a b :=
| mkFunc : forall (x:a), embed a b f x (f x)
.

Arguments embed {a} {b}.

Lemma embed_charac : forall (a b:Type) (f:a -> b) (x:a) (y:b),
    embed f x y <-> f x = y.
Proof.
    intros a b f x y. split; intros H1. 
    - destruct H1. reflexivity.
    - rewrite <- H1. constructor.
Qed.

Lemma embedIsFunction : forall (a b:Type) (f:a -> b), Function (embed f).
Proof.
    intros a b f. split.
    - apply Functional_charac. intros x y y' H1 H2. destruct H1, H2. reflexivity.
    - apply Total_charac. intros x. exists (f x). constructor.
Qed.



