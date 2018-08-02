Require Import eq.
Require Import utils.
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

Lemma permute_inv : forall (v:Type) (p:Eq v) (x y:v), permute p x x y = y.
Proof.
    intros v p x y. unfold permute. destruct (p y x) as [H|H]; subst; 
    reflexivity.
Qed.


Lemma permute_injective : forall (v:Type) (p:Eq v) (x y:v),
    injective (permute p x y).
Proof.
    intros v p x y s t. unfold permute.
    destruct    (p s x) as [Hsx|Hsx], 
                (p t x) as [Htx|Htx]; subst; intros H'.
    - reflexivity.
    - destruct (p t y) as [Hty|Hty]; subst.
        + reflexivity.
        + exfalso. apply Hty. reflexivity.
    - destruct (p s y) as [Hsy|Hsy]; subst.
        + reflexivity.
        + exfalso. apply Hsy. reflexivity.
    - destruct (p s y) as [Hsy|Hsy], (p t y) as [Hty|Hty]; subst.
        + reflexivity.
        + exfalso. apply Htx. reflexivity.
        + exfalso. apply Hsx. reflexivity.
        + reflexivity.
Qed.

Lemma permute_comp : forall (v w:Type) (p:Eq v) (q:Eq w) (x y u:v) (f:v -> w),
    injective f -> f (permute p x y u) = permute q (f x) (f y) (f u).
Proof.
    intros v w p q x y u f I. unfold permute.
    destruct    (p u x) as [Hux|Hux], 
                (p u y) as [Huy|Huy]; subst.
    - destruct (q (f y) (f y)) as [Fyy|Fyy]; reflexivity.
    - destruct (q (f x) (f x)) as [Fxx|Fxx].
        + reflexivity.
        + destruct (q (f x) (f y)) as [Fxy|Fxy].
            { rewrite Fxy. reflexivity. }
            { exfalso. apply Fxx. reflexivity. }
    - destruct (q (f y) (f x)) as [Fyx|Fyx].
        + rewrite Fyx. reflexivity.
        + destruct (q (f y) (f y)) as [Fyy|Fyy].
            { reflexivity. }
            { exfalso. apply Fyy. reflexivity. }
    - destruct (q (f u) (f x)) as [Fux|Fux].
        + exfalso. apply Hux. apply I. assumption.
        + destruct (q (f u) (f y)) as [Fuy|Fuy].
            { exfalso. apply Huy. apply I. assumption. }
            { reflexivity. }
Qed.

Lemma permute_commute : forall (v:Type) (p:Eq v) (x y u:v),
    permute p x y u = permute p y x u.
Proof.
    intros v p x y u. unfold permute.
    destruct (p u x) as [Hx|Hx], (p u y) as [Hy|Hy]; 
    try (reflexivity).
    rewrite <- Hx, <- Hy. reflexivity.
Qed.


Lemma permute_involution : forall (v:Type) (p:Eq v) (x y z:v),
    permute p x y (permute p x y z) = z.
Proof.
    intros v p x y z. unfold permute at 2.
    destruct (p z x) as [Hzx|Hzx], (p z y) as [Hzy|Hzy]; subst.
    - apply permute_x. 
    - apply permute_y.
    - apply permute_x.
    - apply permute_not_xy; assumption.
Qed.


Lemma permute_thrice : forall (v:Type) (p:Eq v) (x y z u:v),
    x <> z  ->
    y <> z  ->
    permute p x y (permute p y z (permute p x y u)) = permute p x z u.
Proof.  
    intros v p x y z u Hxz Hyz.
    unfold permute at 3. destruct (p u x) as [Hux|Hux].
    - rewrite permute_x, Hux, permute_x. apply permute_not_xy;
      apply neq_sym; assumption.
    - destruct (p u y) as [Huy|Huy]; subst.
        + destruct (p x y) as [Hxy|Hxy]; subst.
            { apply permute_inv. }
            { rewrite (permute_not_xy v p y z x); try (assumption).
              rewrite permute_x. symmetry. apply permute_not_xy; assumption.
            }
        + destruct (p x y) as [Hxy|Hxy]; subst.
            { apply permute_inv. }
            { destruct (p u z) as [Huz|Huz]; subst.
                { rewrite permute_y, permute_y, permute_y. reflexivity. }
                { rewrite (permute_not_xy v p y z u); try (assumption).
                  rewrite (permute_not_xy v p x z u); try (assumption).
                  apply permute_not_xy; assumption.
                }
            }
Qed.
                        

(*
    intros v p x y z u Hxy Hxz Hyz.
    unfold permute at 3. destruct (p u x) as [Hux|Hux].
    - rewrite permute_x. rewrite Hux. rewrite permute_x. apply permute_not_xy.
        + apply neq_sym. assumption.
        + apply neq_sym. assumption.
    - destruct (p u y) as [Huy|Huy] eqn:Puy.
        + rewrite (permute_not_xy v p y z x); try (assumption).
            { rewrite permute_x, Huy. symmetry. apply permute_not_xy.
                { apply neq_sym. assumption. }
                { assumption. }
            }
        + unfold permute at 2. rewrite Puy. destruct (p u z) as [Huz|Huz]. 
            { rewrite permute_y, Huz, permute_y. reflexivity. }
            { rewrite permute_not_xy; try (assumption).
              rewrite permute_not_xy; try (assumption). reflexivity.
            }
Qed.
*)
