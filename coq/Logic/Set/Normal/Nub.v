Require Logic.List.Nub.

Require Import Logic.Set.Set.
Require Import Logic.Set.Rank.
Require Import Logic.Set.Equal.

Require Import Logic.Set.Normal.Leq.
Require Import Logic.Set.Normal.Equiv.
Require Import Logic.Set.Normal.InListOf.

(* eliminates syntactic duplicates, not semantics duplicates                    *)
Definition nub (x:set) : set := fromList (Nub.nub (toList x)). 

Definition Nubed (x:set) : Prop := Nub.Nubed (toList x).

Lemma nubInListOfIff : forall (x xs:set),
    inListOf x xs <-> inListOf x (nub xs).
Proof.
    intros x xs. unfold inListOf. unfold nub.
    rewrite toListFromList. apply Nub.nubInIff.
Qed.

Lemma nubEquiv : forall (x:set), Equiv (nub x) x.
Proof.
    intros x. unfold Equiv, nub. rewrite toListFromList.
    apply Nub.nubEquiv.
Qed.

Lemma nubEquivEquiv : forall (x y:set), Equiv x y -> Equiv (nub x) (nub y).
Proof.
    intros x y H. apply equivTrans with x.
    - apply nubEquiv.
    - apply equivTrans with y.
        + assumption.
        + apply equivSym. apply nubEquiv.
Qed.

Lemma nubNubed : forall (x:set), Nubed (nub x).
Proof.
    intros x. unfold Nubed. unfold nub. rewrite toListFromList.
    apply Nub.nubNubed.
Qed.

Lemma nubSame : forall (x:set),
    Nubed x -> nub x = x.
Proof.
    intros x. unfold Nubed. unfold nub. intros H.
    rewrite Nub.nubSame.
    - apply fromListToList.
    - assumption.
Qed.

Lemma nubedConsNotIn : forall (x xs:set),
    Nubed (Cons x xs) -> ~ inListOf x xs.
Proof.
    intros x xs. unfold Nubed. unfold inListOf. simpl.
    apply (Nub.nubedConsNotIn _ _).
Qed.

Lemma nubedConsNubedTail : forall (x xs:set),
    Nubed (Cons x xs) -> Nubed xs.
Proof.
    intros x xs. unfold Nubed. simpl. apply (Nub.nubedConsNubedTail _ _).
Qed. 

Lemma nubEqual : forall (x:set), nub x == x.
Proof.
    intros x. apply equivEqual, nubEquiv.
Qed.

Lemma nubEqual' : forall (x y:set),
    x == y -> nub x == y.
Proof.
    intros x y H. apply equalTrans with x.
    - apply nubEqual.
    - assumption.
Qed.
 
Lemma nubRank : forall (x:set), rank (nub x) = rank x.
Proof.
    intros x. apply rankEqual, nubEqual.
Qed.
