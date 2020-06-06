
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

(* Recursive definition which is accepted by coq.                               *)
Fixpoint normal (x:set) : set :=
    match x with
    | Nil       => Nil
    | Cons x xs => sort (nub (Cons (normal x) (normal xs)))
    end.

(* The real intended definition                                                 *)
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

Inductive Normal (x:set) : Prop :=
| mkNormal : Nubed x -> Sorted x -> 
    (forall (z:set), inListOf z x -> Normal z) -> Normal x.

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
