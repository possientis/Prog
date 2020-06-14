Require Utils.Sort.

Require Import Core.Set.
Require Import Core.Rank.
Require Import Core.Equal.

Require Import Normal.Leq.
Require Import Normal.Equiv.
Require Import Normal.Insert.
Require Import Normal.InListOf.

(* Sorting elements of set as per syntax.                                       *)
Definition sort (x:set) : set := fromList (Sort.sort (toList x)).

Definition Sorted (x:set) : Prop := Sort.Sorted (toList x).

Lemma sortEquiv : forall (x:set), Equiv (sort x) x.
Proof.
    intros x. unfold Equiv, sort. rewrite toListFromList.
    apply Sort.sortEquiv.
Qed.

Lemma sortEquivEquiv : forall (x y:set), Equiv x y -> Equiv (sort x) (sort y).
Proof.
    intros x y H. apply equivTrans with x.
    - apply sortEquiv.
    - apply equivTrans with y.
        + assumption.
        + apply equivSym, sortEquiv.
Qed.

Lemma sortInListOfIff : forall (x xs:set), 
    inListOf x xs <-> inListOf x (sort xs).
Proof.
    intros x xs. unfold inListOf, sort. rewrite toListFromList.
    apply Sort.sortInIff.
Qed.

Lemma insertSorted : forall (x xs:set), 
    Sorted xs -> Sorted (insert x xs).
Proof.
    intros x xs. rewrite insertCorrect. unfold Sorted, insertAsList.
    rewrite toListFromList. apply Sort.insertSorted.
Qed.

Lemma sortSorted : forall (x:set), Sorted (sort x).
Proof.
    intros x. unfold Sorted, sort. rewrite toListFromList. 
    apply Sort.sortSorted.
Qed.

Lemma sortedConsInListOfLeq : forall (x y xs:set),
    Sorted (Cons x xs) -> inListOf y xs -> leq y x.
Proof.
    intros x y xs. unfold Sorted, inListOf. apply Sort.sortedConsInLeq.
Qed.

Lemma sortedCons : forall (x xs:set),
    (forall (z:set), inListOf z xs -> leq z x) -> 
    Sorted xs -> 
    Sorted (Cons x xs).
Proof.
    intros x xs. unfold inListOf, Sorted. intros H1 H2.
    apply (Sort.sortedCons set _ x (toList xs)); assumption.
Qed.

Lemma sortSame : forall (x:set), Sorted x -> sort x = x.
Proof.
    intros x. unfold Sorted, sort. intros H. 
    rewrite <- (fromListToList x) at 2. rewrite Sort.sortSame.
    - reflexivity.
    - assumption.
Qed.

Lemma sortedConsSortedTail : forall (x xs:set),
    Sorted (Cons x xs) -> Sorted xs.
Proof.
    intros x xs. unfold Sorted. simpl. apply Sort.sortedConsSortedTail.
Qed.

Lemma sortEqual : forall (x:set), sort x == x.
Proof.
    intros x. apply equivEqual, sortEquiv.
Qed.

Lemma sortEqual' : forall (x y:set), 
    x == y -> sort x == y.
Proof.
    intros x y H. apply equalTrans with x.
    - apply sortEqual.
    - assumption.
Qed.

Lemma sortRank : forall (x:set), rank (sort x) = rank x.
Proof.
    intros x. apply rankEqual, sortEqual.
Qed.

