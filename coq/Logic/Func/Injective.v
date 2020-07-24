Require Import List.

Require Import Logic.Func.Composition.

Definition injective (v w:Type) (f:v -> w) : Prop :=
    forall (x y:v), f x = f y -> x = y.

Arguments injective {v} {w} _.


Lemma injective_comp : forall (v w u:Type) (f:v -> w) (g:w -> u),
    injective f -> injective g -> injective (g ; f).
Proof.
    intros v w u f g If Ig x y H. apply If. apply Ig. assumption.
Qed.
