Require Import Core.Set.
Require Import Core.Leq.
Require Import Core.Elem.
Require Import Core.Cons.
Require Import Core.Equal.
Require Import Core.Decidability.

(* Insert the set x inside the set y according to syntactic ordering.           *)
Fixpoint insert (x y:set) : set :=
    match y with
    | Nil           => Cons x Nil
    | (Cons y ys)   =>
        match (leqDec x y) with
        | left _    => Cons y (insert x ys)     (* x 'smaller' goes inside      *)
        | right _   => Cons x (Cons y ys)
        end
    end.

Lemma insertCons : forall (x xs:set), insert x xs == Cons x xs.
Proof.
    intros x ys. revert ys x. induction ys as [|y IH1 ys IH2]; intros x.
    - apply equalRefl.
    - simpl. destruct (leqDec x y) as [H|H].
        + apply equalTrans with (Cons y (Cons x ys)).
            { apply consCompatR. apply IH2. }
            { apply consSwitch. }
        + apply equalRefl.
Qed.

Lemma insertCompatL : forall (x x' y:set), x == x' -> insert x y == insert x' y.
Proof.
    intros x x' y H. apply equalTrans with (Cons x y).
    - apply insertCons.
    - apply equalTrans with (Cons x' y).
        + apply consCompatL. assumption.
        + apply equalSym. apply insertCons.
Qed.



Lemma insertCompatR : forall (x y y':set), y == y' -> insert x y == insert x y'.
Proof.
    intros x y y' H. apply equalTrans with (Cons x y).
    - apply insertCons.
    - apply equalTrans with (Cons x y').
        + apply consCompatR. assumption.
        + apply equalSym. apply insertCons.
Qed.


Lemma insertCompatLR : forall (x x' y y':set), 
    x == x' -> y == y' -> insert x y == insert x' y'.
Proof.
    intros x x' y y' Hx Hy. apply equalTrans with (insert x' y).
    - apply insertCompatL. assumption.
    - apply insertCompatR. assumption.
Qed.
