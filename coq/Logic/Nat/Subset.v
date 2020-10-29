Require Import Le.

Require Import Logic.Class.Ord.
Require Import Logic.Nat.Ord.
Require Import Logic.Nat.Leq.

(* Subset of N defined as predicate over N                                      *)
Definition Subset : Type := nat -> Prop.

(* n is an element of subset A.                                                 *)
Definition Elem (n:nat) (A:Subset) : Prop := A n.

Notation "n :: A" := (Elem n A) : Nat_Subset_scope.

Open Scope Nat_Subset_scope.

(* n is the smallest element of A.                                              *)
Definition Smallest (n:nat) (A:Subset) : Prop :=
    (n :: A) /\ forall (m:nat), m :: A -> n <= m.

(* A is a finite subset of N.                                                   *)
Definition Finite (A:Subset) : Prop :=
    exists (n:nat), forall (m:nat), m :: A -> m <= n.

(* A /\ [0,n]                                                                   *)
Definition restrict (n:nat) (A:Subset) : Subset :=
    fun (m:nat)  => m :: A /\ m <= n.

(* All restricted subsets are finite.                                           *)
Lemma restrictFinite : forall (A:Subset) (n:nat), Finite (restrict n A).
Proof.
    intros A n. exists n. intros m [H1 H2]. assumption.
Qed.

(* If n belongs to A, being the smallest element of A is the same as being the  *)
(* smallest element of A /\ [0, n].                                             *)
Lemma smallestRestrict : forall (A:Subset) (n m:nat), n :: A ->
    Smallest m A <-> Smallest m (restrict n A).
Proof.
    intros A n m H1. split.
    - intros [H2 H3]. split.
        + split; try assumption. apply H3. assumption.
        + intros k [H4 H5]. apply H3. assumption.
    - intros [[H2 H3] H4]. split; try assumption. intros k H5.
      destruct (leqTotal k n) as [H6|H6].
        + apply H4. split; assumption.
        + apply le_trans with n; assumption.
Qed.

(*
Lemma nonEmptyFiniteHasSmallest : forall (A:Subset),
    (exists (k:nat), k :: A) -> 
    Finite A                 -> 
    (exists (k:nat), Smallest k A).

Proof.
    unfold Finite, Smallest. intros A H2 [n H1]. revert n A H1 H2.
    induction n as [|n IH]; intros A H1 [m H2].
    - assert (m = 0) as H3. { apply le_0, H1. assumption. }
      subst. exists 0. split; try assumption. intros m H3. apply le_0_n.
    -
Show.
*)

(*
Lemma ex_imp_small : forall (p:nat -> Prop), 
    (exists (n:nat), p n ) -> exists (n:nat), asSmallest p n.
Proof.
    unfold asSmallest. intros p [n H1].

Show.
*)



(*
Definition witnessNat (p:nat -> Prop) (q:Dec p) (r:exists (n:nat), p n) : nat :=
    proj1_sig (witness p q r).

Lemma witnessSound : forall (p:nat -> Prop) (q:Dec p) (r:exists (n:nat), p n),
    p (witnessNat p q r).
Proof.
    intros p q r. exact (proj2_sig (witness p q r)).
Qed.


Lemma witnessSmallest : forall (p:nat -> Prop) (q:Dec p) (r:exists (n:nat), p n),
    forall (n:nat), p n -> witnessNat p q r <= n.
Proof.

Show.
*)

