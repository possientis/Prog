Require Import List.

Require Import Eq.
Require Import Replace.
Require Import Coincide.
Require Import Injective.
Require Import Composition.
Require Import Extensionality.

(* permutes x and y                                                             *)
Definition permute (v:Type) (p:Eq v) (x y:v) (u:v) : v :=
    match p u x with
    | left  _       => y        (* if u = x return y    *)
    | right _       =>
        match p u y with
        | left  _   => x        (* if u = y return x    *)
        | right _   => u        (* otherwise return u   *)
        end
     end.

Arguments permute {v} _ _ _ _.


Lemma permute_comp : forall (v w:Type) (p:Eq v) (q:Eq w) (x y:v) (f:v -> w),
    injective f -> f ; (permute p x y) = permute q (f x) (f y) ; f.
Proof.
    intros v w p q x y f I. apply extensionality. 
    intros u. unfold permute, comp.
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


Lemma permute_replace : forall (v:Type) (p:Eq v) (x y:v) (xs: list v),
    ~(In y xs) -> coincide xs (replace p x y) (permute p x y).
Proof.
    intros v p x y xs H. unfold coincide. intros u H'.
    destruct    (p u x) as [Hux|Hux] eqn:Eux, 
                (p u y) as [Huy|Huy] eqn:Euy; 
    subst; unfold permute, replace.
    - exfalso. apply H. assumption.
    - destruct (p x x) as [Hxx|Hxx].
        + reflexivity.
        + destruct (p x y); reflexivity. 
    - exfalso. apply H. assumption.
    - rewrite Eux, Euy. reflexivity.
Qed.

