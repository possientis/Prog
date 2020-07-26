Require Logic.List.Sort.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Cons.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Decidable.

Require Import Logic.Set.Normal.Leq.
Require Import Logic.Set.Normal.Ord.
Require Import Logic.Set.Normal.Equiv.
Require Import Logic.Set.Normal.InListOf.

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

Definition insertAsList (x xs:set) : set :=
    fromList (Sort.insert x (toList xs)).

Lemma insertCorrect : forall (x y:set), insert x y = insertAsList x y.
Proof.
    intros x y. revert x. revert y. induction y as [|y _ ys IH]; intros x.
    - reflexivity.
    - unfold insertAsList. simpl. destruct (leqDec x y) as [H|H]; simpl.
        + rewrite IH. reflexivity.
        + rewrite fromListToList. reflexivity.
Qed.

Lemma insertEquivCons : forall (x xs:set), Equiv (insert x xs) (Cons x xs).
Proof.
    intros x xs. unfold Equiv. rewrite insertCorrect. unfold insertAsList.
    rewrite toListFromList. simpl. apply Sort.insertEquivCons. 
Qed.

Lemma insertInListOf : forall (x xs:set), inListOf x (insert x xs).
Proof.
    intros x xs. rewrite insertCorrect. unfold inListOf, insertAsList.
    rewrite toListFromList. apply Sort.insertIn.
Qed.

Lemma insertIsCons : forall (x xs:set), 
    (forall (y:set), inListOf y xs -> leq y x) -> insert x xs = Cons x xs.
Proof.
    intros x xs. rewrite insertCorrect. unfold inListOf, insertAsList.
    intros H. rewrite <- (fromListToList (Cons x xs)).
    rewrite Sort.insertIsCons.
    - reflexivity.
    - assumption.
Qed.


Lemma insertCons : forall (x xs:set), insert x xs == Cons x xs.
Proof.
    intros x xs. apply Equiv.equivEqual. apply insertEquivCons.
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

