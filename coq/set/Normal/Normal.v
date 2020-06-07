
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

Require Import Normal.Map.
Require Import Normal.Leq.
Require Import Normal.Nub.
Require Import Normal.Sort.
Require Import Normal.Equiv.
Require Import Normal.Insert.
Require Import Normal.InListOf.

(* Nubing a sorted set yields a sorted set.                                     *)
Lemma nubSorted : forall (x:set), Sorted x -> Sorted (nub x).
Proof.
    intros x. unfold Sorted, nub. rewrite toListFromList.
    apply Normal.nubSorted.
Qed.

(* Inserting a set not already present into a nubed set, yields a nubed set.    *)
Lemma insertNubed : forall (x xs:set),
    ~ inListOf x xs -> Nubed xs -> Nubed (insert x xs).
Proof.
    intros x xs. rewrite insertCorrect. unfold inListOf, Nubed, insertAsList.
    rewrite toListFromList. apply Normal.insertNubed.
Qed.

(* Sorting a nubed set yields a nubed set.                                      *)
Lemma sortNubed : forall (x:set), Nubed x -> Nubed (sort x).
Proof.
    intros x. unfold Nubed, sort. 
    rewrite toListFromList. apply Normal.sortNubed.
Qed.

(* Two sorted sets which are equivalent as lists have identical heads.          *)
Lemma sameHead : forall (x y xs ys:set),
    Equiv (Cons x xs) (Cons y ys) ->
    Sorted (Cons x xs) ->
    Sorted (Cons y ys) ->
    x = y.
Proof.
    intros x y xs ys. unfold Equiv, Sorted. simpl.
    apply Normal.sameHead.
Qed.

(* Two sorted and nubed sets which are equivalent as lists are identical.       *) 
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

(* nubbing and sorting commute with each other.                                 *)
Lemma nubSortCommute : forall (x:set), nub (sort x) = sort (nub x).
Proof.
    intros x. unfold nub, sort. rewrite toListFromList, toListFromList.
    rewrite Normal.nubSortCommute. reflexivity.
Qed.

(* Normalizing a set: recursive definition which is accepted by coq.            *)
Fixpoint normal (x:set) : set :=
    match x with
    | Nil       => Nil
    | Cons x xs => sort (nub (Cons (normal x) (normal xs)))
    end.

(* The real intended definition.                                                *)
Lemma normalDef : forall (x:set),
    normal x = sort (nub (map normal x)).
Proof.
    induction x as [|x IH1 xs IH2].
    - reflexivity.
    - simpl. apply nubedSortedEquivSame.
        + apply sortNubed, nubNubed.
        + apply sortNubed, nubNubed.
        + apply sortSorted.
        + apply sortSorted.
        + rewrite mapCons. apply sortEquivEquiv, nubEquivEquiv, equivConsCompat.
          rewrite IH2. apply equivTrans with (nub (map normal xs)).
            { apply equivSym, sortEquiv. }
            { apply equivSym, nubEquiv. }
Qed.

(* Predicate expressing the fact that a set is in normal form:                  *)
(* A set is in normal form when it has been Nubed and Sorted,                   *)
(* and every element of its list is itself in normal form.                      *)
Inductive Normal (x:set) : Prop :=
| mkNormal : 
    Nubed x  -> 
    Sorted x -> 
    (forall (z:set), inListOf z x -> Normal z) -> 
    Normal x
.

Lemma normalEqual : forall (x:set), x == normal x.
Proof.
    induction x as [|x IH1 xs IH2].
    - apply equalRefl.
    - unfold normal. fold normal. 
      apply sortEqual', nubEqual', consCompatLR; assumption.
Qed.

Lemma normalRank : forall (x:set), rank (normal x) = rank x.
Proof.
    intros x. apply rankEqual, equalSym, normalEqual.
Qed.



Lemma normalNubed : forall (x:set), Nubed (normal x).
Proof.
    intros x. rewrite normalDef. apply sortNubed, nubNubed.
Qed.

Lemma normalSorted : forall (x:set), Sorted (normal x).
Proof.
    intros x. rewrite normalDef. apply sortSorted.
Qed.

Lemma NilNormal : Normal Nil.
Proof.
    constructor.
    - constructor.
    - constructor.
    - intros z H. inversion H.
Qed.

(*
Lemma normalNormal : forall (x:set), Normal (normal x).
Proof.
    (* setting up induction on rank x.                                          *)
    intros x. remember (rank x) as n eqn:E. 
    assert (rank x <= n) as H. { rewrite E. apply le_n. } 
    clear E. revert H. revert x. revert n.
    induction n as [|n IH]; intros x H1.
    - inversion H1 as [H2|]. apply rankNil in H2. rewrite H2. apply NilNormal.
    - constructor.
        + apply normalNubed.
        + apply normalSorted.
        + intros z H2. unfold inListOf in H2. apply rankToList in H2.
Show.
*)

