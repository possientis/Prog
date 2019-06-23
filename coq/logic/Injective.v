Require Import List.

Require Import Composition.

Definition injective (v w:Type) (f:v -> w) : Prop :=
    forall (x y:v), f x = f y -> x = y.


Arguments injective {v} {w} _.

Open Scope Composition.

Lemma injective_comp : forall (v w u:Type) (f:v -> w) (g:w -> u),
    injective f -> injective g -> injective (g ; f).
Proof.
    intros v w u f g If Ig x y H. apply If. apply Ig. assumption.
Qed.

Definition injective_on (v w:Type) (xs:list v) (f:v -> w) : Prop :=
    forall (x y:v), In x xs -> In y xs -> f x = f y -> x = y. 

Arguments injective_on {v} {w} _ _.

Lemma injective_on_appl : forall (v w:Type) (xs ys:list v) (f:v -> w),
    injective_on (xs ++ ys) f -> injective_on xs f.
Proof.
    intros v w xs ys f H x y Hx Hy H'.
    apply H; simpl.
    - apply in_or_app. left. assumption.
    - apply in_or_app. left. assumption.
    - assumption.
Qed.

Lemma injective_on_appr : forall (v w:Type) (xs ys:list v) (f:v -> w),
    injective_on (xs ++ ys) f -> injective_on ys f.
Proof.
    intros v w xs ys f H x y Hx Hy H'.
    apply H; simpl.
    - apply in_or_app. right. assumption.
    - apply in_or_app. right. assumption.
    - assumption.
Qed.

Lemma injective_on_cons : forall (v w:Type) (x:v) (xs:list v) (f:v -> w),
    injective_on (x :: xs) f -> injective_on xs f.
Proof.
    intros v w x xs f H x1 x2 H1 H2 H'.
    apply H; simpl.
    - right. assumption.
    - right. assumption.
    - assumption.
Qed.



