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


Lemma permute_comp : forall (v w:Type) (p:Eq v) (q:Eq w) (x y u:v) (f:v -> w),
    injective f -> f (permute p x y u) = permute q (f x) (f y) (f u).
Proof.
    intros v w p q x y u f I. unfold permute.
    destruct    (p u x) as [Hux|Hux], 
                (p u y) as [Huy|Huy],
                (q (f u) (f x)) as [Gux|Gux],
                (q (f u) (f y)) as [Guy|Guy];
    subst;
    try (reflexivity).
    - exfalso. apply Gux. reflexivity.
    - exfalso. apply Gux. reflexivity.
    - symmetry. assumption.
    - symmetry. assumption.
    - exfalso. apply Guy. reflexivity.
    - assumption.
    - exfalso. apply Hux. apply I. assumption.
    - exfalso. apply Huy. apply I. assumption.
Qed.

Lemma permute_commute : forall (v:Type) (p:Eq v) (x y u:v),
    permute p x y u = permute p y x u.
Proof.
    intros v p x y u. unfold permute.
    destruct (p u x) as [Hx|Hx], (p u y) as [Hy|Hy]; 
    try (reflexivity).
    rewrite <- Hx, <- Hy. reflexivity.
Qed.


Lemma permute_involution : forall (v:Type) (p:Eq v) (x y u:v),
    permute p x y (permute p x y u) = u.
Proof.
    intros v p x y u. unfold permute.
    destruct (p u x) as [Hx|Hx] eqn:Px, (p u y) as [Hy|Hy] eqn:Py;
    try (rewrite Px); try (rewrite Py);
    destruct    (p y x) as [Hyx|Hyx], 
                (p x y) as [Hxy|Hxy],
                (p x x) as [Hxx|Hxx],
                (p y y) as [Hyy|Hyy];
    subst; try (reflexivity).
    - exfalso. apply Hyy. reflexivity.
    - exfalso. apply Hyy. reflexivity.
    - exfalso. apply Hxx. reflexivity.
    - exfalso. apply Hxx. reflexivity.
Qed.

    




