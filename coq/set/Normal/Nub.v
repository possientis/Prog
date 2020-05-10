Require Utils.Nub.

Require Import Core.Set.

Require Import Normal.Leq.
Require Import Normal.Equiv.
Require Import Normal.InListOf.

(* eliminates syntactic duplicates, not semantics duplicates                    *)
Definition nub (x:set) : set := fromList (Nub.nub (toList x)). 

Definition Nubed (x:set) : Prop := Nub.Nubed (toList x).

Lemma nubInListOfIff : forall (x xs:set),
    inListOf x xs <-> inListOf x (nub xs).
Proof.
    intros x xs. unfold inListOf. unfold nub.
    rewrite toListFromList. apply Nub.nubInIff.
Qed.

Lemma nubEquiv : forall (x:set), Equiv x (nub x).
Proof.
    intros x. unfold Equiv. unfold nub. rewrite toListFromList.
    apply Nub.nubEquiv.
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
    
