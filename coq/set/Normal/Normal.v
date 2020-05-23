Require Import List.

Require Import Utils.Ord.

Require Utils.Normal.

Require Import Core.Set.
Require Import Core.Incl.
Require Import Core.Elem.
Require Import Core.Cons.
Require Import Core.Rank.
Require Import Core.Equal.
Require Import Core.Order.
Require Import Core.Empty.
Require Import Core.ElemIncl.
Require Import Core.Decidability.
Require Import Core.Extensionality.

Require Import Normal.Leq.
Require Import Normal.Nub.
Require Import Normal.Sort.
Require Import Normal.Equiv.
Require Import Normal.Insert.
Require Import Normal.InListOf.

Fixpoint normal (x:set) : set :=
    match x with
    | Nil           => Nil
    | (Cons x xs)   =>
        match (elem_dec x xs) with
        | left _    => normal xs                        (*  we have x :: xs     *)
        | right _   => insert (normal x) (normal xs)    (*  otherwise           *)
        end
    end.


Lemma normalEqual : forall (x:set), x == normal x.
Proof.
    induction x as [|x IH1 xs IH2].
    - apply equalRefl.
    - simpl. destruct (elem_dec x xs) as [H|H]; simpl.
        +  apply equalTrans with xs.
            { apply inConsEqual. assumption. }
            { apply IH2. }
        + apply equalTrans with (insert x xs).
            { apply equalSym. apply insertCons. }
            { apply insertCompatLR.
                { apply IH1. }
                { apply IH2. }}
Qed.

Lemma normalSameEqual : forall (x y:set), normal x = normal y -> x == y.
Proof.
    intros x y H. apply equalTrans with (normal y).
    - apply equalTrans with (normal x).
        + apply normalEqual.
        + rewrite H. apply equalRefl.
    - apply equalSym. apply normalEqual.
Qed.

Lemma nubSorted : forall (x:set), Sorted x -> Sorted (nub x).
Proof.
    intros x. unfold Sorted, nub. rewrite toListFromList.
    apply Normal.nubSorted.
Qed.

Lemma insertNubed : forall (x xs:set),
    ~ inListOf x xs -> Nubed xs -> Nubed (insert x xs).
Proof.
    intros x xs. rewrite insertCorrect. unfold inListOf, Nubed, insertAsList.
    rewrite toListFromList. apply Normal.insertNubed.
Qed.

Lemma sortNubed : forall (x:set), Nubed x -> Nubed (sort x).
Proof.
    intros x. unfold Nubed, sort. 
    rewrite toListFromList. apply Normal.sortNubed.
Qed.


Lemma sameHead : forall (x y xs ys:set),
    Equiv (Cons x xs) (Cons y ys) ->
    Sorted (Cons x xs) ->
    Sorted (Cons y ys) ->
    x = y.
Proof.
    intros x y xs ys. unfold Equiv, Sorted. simpl.
    apply Normal.sameHead.
Qed.

Lemma nubedSortedEquivSame : forall (x y:set),
    Nubed x ->
    Nubed y ->
    Sorted x ->
    Sorted y ->
    Equiv x y ->
    x = y.
Proof.
    intros x y. unfold Nubed, Sorted, Equiv.
    intros H1 H2 H3 H4 H5. 
    rewrite <- (fromListToList x).
    rewrite <- (fromListToList y).
    assert (toList x = toList y) as H6.
        { apply (Normal.nubedSortedEquivSame _ _); assumption. } 
    rewrite H6. reflexivity.
Qed.

Lemma nubSortCommute : forall (x:set), nub (sort x) = sort (nub x).
Proof.
    intros x. unfold nub, sort. rewrite toListFromList, toListFromList.
    rewrite Normal.nubSortCommute. reflexivity.
Qed.

Definition normalAsList (x:set) : set :=
    fromList (Normal.normal (map normal (toList x))).

(*
Lemma normalCorrect : forall (n:nat) (x:set), rank x <= n ->
    toList (normal x) = Normal.normal (map normal (toList x)).
Proof.
    induction n as [|n IH]; intros x H1.
    - admit.
    - destruct x as [|x xs].
        + reflexivity.
        + simpl. destruct (elem_dec x xs) as [H2|H2].
            { admit. }
            {

Show.
*)

