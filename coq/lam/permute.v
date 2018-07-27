Require Import eq.
Require Import injective.

(* defines a map v -> v which permutes x and y                      *)
Definition permute (v:Type) (p:Eq v) (x y:v) (u:v) : v :=
    match p u x with
    | left  _       => y        (* if u = x return y    *)
    | right _       =>
        match p u y with
        | left  _   => x        (* if u = y return x    *)
        | right _   => u        (* otherwise return u   *)
        end
     end.

Arguments permute {v} _ _ _.

Lemma permute_x : forall (v:Type) (p:Eq v) (x y:v), permute p x y x = y.
Proof.
    intros v p x y. unfold permute. destruct (p x x) as [H|H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
Qed.

Lemma permute_y : forall (v:Type) (p: Eq v) (x y:v), permute p x y y = x.
Proof.
    intros v p x y. unfold permute.
    destruct (p y x) as [H0|H0].
    - assumption.
    - destruct (p y y) as [H1|H1].
        + reflexivity.
        + exfalso. apply H1. reflexivity.
Qed.

Lemma permute_not_xy : forall (v:Type) (p:Eq v) (x y z:v),
    z <> x -> z <> y -> permute p x y z = z.
Proof.
    intros v p x y z Hx Hy. unfold permute. 
    destruct (p z x) as [H0|H0].
    - exfalso. apply Hx. assumption.
    - destruct (p z y) as [H1|H1].
        + exfalso. apply Hy. assumption.
        + reflexivity.
Qed.


Lemma permute_injective : forall (v:Type) (p:Eq v) (x y:v),
    injective (permute p x y).
Proof.
    intros v p x y s t. unfold permute.
    destruct    (p s x) as [Hsx|Hsx], 
                (p t x) as [Htx|Htx],
                (p s y) as [Hsy|Hsy],
                (p t y) as [Hty|Hty]; 
    subst; 
    try (reflexivity); intros H;
    try (assumption); subst;
    try (reflexivity).
    - exfalso. apply Hty. reflexivity.
    - exfalso. apply Hsy. reflexivity.
    - exfalso. apply Htx. reflexivity.
    - exfalso. apply Hsx. reflexivity. 
Qed.


