Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Func.Injective.
Require Import Logic.Func.Composition.

Require Import Logic.Axiom.Extensionality.

(* permutes x and y                                                             *)
Definition permute (v:Type) (e:Eq v) (x y:v) (u:v) : v :=
    match eqDec u x with
    | left  _       => y        (* if u = x return y    *)
    | right _       =>
        match eqDec u y with
        | left  _   => x        (* if u = y return x    *)
        | right _   => u        (* otherwise return u   *)
        end
     end.

Arguments permute {v} {e} _ _ _.

Notation "x <:> y" := (permute y x)
    (at level 70, no associativity) : Permute_scope.

Open Scope Permute_scope.


Lemma permute_comp : forall (v w:Type) (e:Eq v) (e':Eq w) (x y:v) (f:v -> w),
    injective f -> f ; (y <:> x) = (f y <:> f x) ; f.
Proof.
    intros v w e e' x y f I. apply extensionality. 
    intros u. unfold permute, comp.
    destruct    (eqDec u x) as [Hux|Hux], 
                (eqDec u y) as [Huy|Huy]; subst.
    - destruct (eqDec (f y) (f y)) as [Fyy|Fyy]; reflexivity.
    - destruct (eqDec (f x) (f x)) as [Fxx|Fxx].
        + reflexivity.
        + destruct (eqDec (f x) (f y)) as [Fxy|Fxy].
            { rewrite Fxy. reflexivity. }
            { exfalso. apply Fxx. reflexivity. }
    - destruct (eqDec (f y) (f x)) as [Fyx|Fyx].
        + rewrite Fyx. reflexivity.
        + destruct (eqDec (f y) (f y)) as [Fyy|Fyy].
            { reflexivity. }
            { exfalso. apply Fyy. reflexivity. }
    - destruct (eqDec (f u) (f x)) as [Fux|Fux].
        + exfalso. apply Hux. apply I. assumption.
        + destruct (eqDec (f u) (f y)) as [Fuy|Fuy].
            { exfalso. apply Huy. apply I. assumption. }
            { reflexivity. }
Qed.

