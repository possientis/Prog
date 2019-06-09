Require Import List.

Require Import Eq.
Require Import Replace.
Require Import Coincide.
Require Import Injective.
Require Import Composition.
Require Import Extensionality.

(* permutes x and y                                                             *)
Definition permute (v:Type) (e:Eq v) (x y:v) (u:v) : v :=
    match e u x with
    | left  _       => y        (* if u = x return y    *)
    | right _       =>
        match e u y with
        | left  _   => x        (* if u = y return x    *)
        | right _   => u        (* otherwise return u   *)
        end
     end.

Arguments permute {v} _ _ _ _.


Lemma permute_comp : forall (v w:Type) (e:Eq v) (e':Eq w) (x y:v) (f:v -> w),
    injective f -> f ; (permute e x y) = permute e' (f x) (f y) ; f.
Proof.
    intros v w e e' x y f I. apply extensionality. 
    intros u. unfold permute, comp.
    destruct    (e u x) as [Hux|Hux], 
                (e u y) as [Huy|Huy]; subst.
    - destruct (e' (f y) (f y)) as [Fyy|Fyy]; reflexivity.
    - destruct (e' (f x) (f x)) as [Fxx|Fxx].
        + reflexivity.
        + destruct (e' (f x) (f y)) as [Fxy|Fxy].
            { rewrite Fxy. reflexivity. }
            { exfalso. apply Fxx. reflexivity. }
    - destruct (e' (f y) (f x)) as [Fyx|Fyx].
        + rewrite Fyx. reflexivity.
        + destruct (e' (f y) (f y)) as [Fyy|Fyy].
            { reflexivity. }
            { exfalso. apply Fyy. reflexivity. }
    - destruct (e' (f u) (f x)) as [Fux|Fux].
        + exfalso. apply Hux. apply I. assumption.
        + destruct (e' (f u) (f y)) as [Fuy|Fuy].
            { exfalso. apply Huy. apply I. assumption. }
            { reflexivity. }
Qed.


Lemma permute_replace : forall (v:Type) (e:Eq v) (x y:v) (xs: list v),
    ~(In y xs) -> coincide xs (replace e x y) (permute e x y).
Proof.
    intros v e x y xs H. unfold coincide. intros u H'.
    destruct    (e u x) as [Hux|Hux] eqn:Eux, 
                (e u y) as [Huy|Huy] eqn:Euy; 
    subst; unfold permute, replace.
    - exfalso. apply H. assumption.
    - destruct (e x x) as [Hxx|Hxx].
        + reflexivity.
        + destruct (e x y); reflexivity. 
    - exfalso. apply H. assumption.
    - rewrite Eux, Euy. reflexivity.
Qed.

