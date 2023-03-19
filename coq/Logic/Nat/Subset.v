Require Import Le.

Require Import Logic.Axiom.Wec.
Require Import Logic.Axiom.Dec.
Require Import Logic.Axiom.Witness.

Require Import Logic.Class.Ord.

Require Import Logic.Nat.Ord.
Require Import Logic.Nat.Leq.
Require Import Logic.Nat.Wec.
Require Import Logic.Nat.Dec.

Declare Scope Nat_Subset_scope.

(* Subset of N defined as predicate over N                                      *)
Definition Subset : Type := nat -> Prop.

(* n is an element of subset A.                                                 *)
Definition Elem (n:nat) (A:Subset) : Prop := A n.

Notation "n :: A" := (Elem n A) : Nat_Subset_scope.

Open Scope Nat_Subset_scope.

(* n is the smallest element of A.                                              *)
Definition SmallestOf (A:Subset) (n:nat) : Prop :=
    (n :: A) /\ forall (m:nat), m :: A -> n <= m.

(* A is a finite subset of N.                                                   *)
Definition Finite (A:Subset) : Prop :=
    exists (n:nat), forall (m:nat), m :: A -> m <= n.

(* A /\ [0,n]                                                                   *)
Definition restrict (n:nat) (A:Subset) : Subset :=
    fun (m:nat)  => m :: A /\ m <= n.

Lemma restrictWec : forall (A:Subset) (n:nat), pWec A -> pWec (restrict n A).
Proof.
    intros A n H1 k. apply andWec.
    - apply H1.
    - apply DecWec, leqDec.
Defined.

(* All restricted subsets are finite.                                           *)
Lemma restrictFinite : forall (A:Subset) (n:nat), Finite (restrict n A).
Proof.
    intros A n. exists n. intros m [H1 H2]. assumption.
Defined.


(* If A /\ [0,n] is non-empty, being the smallest element of A is the same as   *)
(* being the smallest element of A /\ [0, n].                                   *)
Lemma restrictSmallest : forall (A:Subset) (n m:nat), 
    (exists (k:nat), k :: restrict n A) ->
    SmallestOf A m <-> SmallestOf (restrict n A) m.
Proof.
    intros A n m [k [H1 H2]]. split.
    - intros [H3 H4]. split.
        + split; try assumption. apply le_trans with k; try assumption.
          apply H4. assumption.
        + intros p [H5 H6]. apply H4. assumption.
    - intros [[H3 H4] H5]. split; try assumption. intros p H6.
      destruct (leqTotal p n) as [H7|H7].
        + apply H5. split; assumption.
        + apply le_trans with n; assumption.
Defined.

Lemma nonEmptyFiniteHasSmallest : forall (A:Subset),
    pWec A                   ->     (* A is weakly decidable *)
    (exists (k:nat), k :: A) -> 
    Finite A                 -> 
    (exists (k:nat), SmallestOf A k).

Proof.
    intros A W H2 [n H1]. revert n A W H1 H2.
    induction n as [|n IH]; intros A W H1 [m H2].
    - assert (m = 0) as H3. { apply le_0, H1. assumption. }
      subst. exists 0. split; try assumption. intros m H3. apply le_0_n.
    - destruct (boundedWec A W n) as [H3|H3]. 
        + destruct H3 as [m' [H3 H4]].
          assert (exists (k:nat), SmallestOf (restrict n A) k) as H5. 
            {apply IH.
                { apply  restrictWec. assumption. }
                { intros k [H5 H6]. assumption. }
                { exists m'. split; assumption. }}
          destruct H5 as [k H5]. exists k. rewrite (restrictSmallest A n k);
          try assumption. exists k. destruct H5 as [H5 H6]. assumption.
        + exists m. split; try assumption. intros k H4.
          assert (k = S n) as H5. 
            { apply le_antisym.
                { apply H1. assumption. }
                { destruct (leqDec k n) as [H5|H5].
                    { exfalso. apply H3. exists k. split; assumption. }
                    { apply not_le_ge. assumption. }}}
          rewrite H5. apply H1. assumption. 
Defined.

Theorem nonEmptyHasSmallest : forall (A:Subset),
    pWec A                   ->
    (exists (k:nat), k :: A) ->
    (exists (k:nat), SmallestOf A k).
Proof.
    intros A W [k H1]. 
    assert (exists (m:nat), SmallestOf (restrict k A) m) as H2.
    { apply nonEmptyFiniteHasSmallest.
        { apply restrictWec. assumption. }
        { exists k. split; try assumption. apply le_n. }
        { apply restrictFinite. }}
    destruct H2 as [m H2]. exists m. 
    apply restrictSmallest in H2; try assumption. exists k. 
    split; try assumption. apply le_n.
Defined.


(* If a subset is computationally decidable, then so is the predicate which     *)
(* expresses the fact that a natural number is its smallest element.            *)
Lemma DecSmallest : forall (A:Subset), pDec A -> pDec (SmallestOf A).
Proof.
    intros A H1 n. destruct n as [|n]. 
    - destruct (H1 0) as [H2|H2]. 
        + left. split; try assumption. intros m H3. apply le_0_n.
        + right. intros [H3 H4]. apply H2. assumption.
    - remember (boundedDec A H1 n) as H2 eqn:E. clear E. destruct H2 as [H2|H2].
        + right. intros [H3 H4]. destruct H2 as [m [H2 H5]].
          apply not_le_Sn_n with n. apply le_trans with m; try assumption.
          apply H4. assumption.
        + destruct (H1 (S n)) as [H3|H3].
            { left. split; try assumption. intros m H4.
              destruct (leqDec m n) as [H5|H5].
                { exfalso. apply H2. exists m. split; assumption. }
                { apply not_le_ge. assumption. }}
            { right. intros [H4 H5]. apply H3 in H4. contradiction. }
Defined.

(* Function which given a subset, a proof of it computational decidability,     *)
(* a proof of its non-emptiness, returns its smallest element.                  *)
Definition smallestOf (A:Subset) (p:pDec A) (q:exists (k:nat), k :: A) : nat :=
    proj1_sig 
        (witness 
            (SmallestOf A) 
            (DecSmallest A p) 
            (nonEmptyHasSmallest A (pDecWec nat A p) q)).


Lemma smallestOfSound : 
    forall (A:Subset) (p:pDec A) (q:exists (k:nat), k :: A),
        SmallestOf A (smallestOf A p q).
Proof.
    intros A p q. exact (
        proj2_sig 
            (witness 
                (SmallestOf A) 
                (DecSmallest A p) 
                (nonEmptyHasSmallest A (pDecWec nat A p) q))).
Defined.

(*
Definition ex1 : Subset := fun n => n * n = 144.

Lemma ex1Dec : pDec ex1.
Proof.
    unfold ex1. intros n. exact (eqDec (n*n) 144).
Defined.

Lemma ex1NonEmpty : exists (k:nat), k :: ex1.
Proof.
    exists 12. reflexivity.
Defined.

Compute smallestOf ex1 ex1Dec ex1NonEmpty.
*)

