Require Import Le.

Require Import Logic.Class.Ord.
Require Import Logic.Nat.Ord.

(* Transform a predicate into another predicate which is satisfied when the     *)
(* argument predicate is satisfied and it is the smallest value doing so, i.e.  *)
(* 'small p n' <-> 'n is the smallest value satisfying the predicate p'.        *)
Definition small (p:nat -> Prop) (n:nat) : Prop :=
    p n /\ forall (m:nat), p m -> n <= m.

(* Expresses the idea that a predicate represents a finite subset of N.         *)
Definition Finite (p:nat -> Prop) : Prop :=
    exists (n:nat), forall (m:nat), p m -> m <= n.

Definition truncate (p:nat -> Prop) (n:nat) : nat -> Prop :=
    fun (m:nat) => p m /\ m <= n.

Lemma truncateFinite : forall (p:nat -> Prop) (n:nat), Finite (truncate p n). 
Proof.
    intros p n. unfold Finite, truncate. exists n. intros m [H1 H2]. assumption.
Qed.

Lemma truncateSmall : forall (p:nat -> Prop) (n m:nat), p n ->
    small p m <-> small (truncate p n) m.
Proof.
    intros p n m H1. unfold small, truncate. split.
    - intros [H2 H3]. split.
        + split; try assumption. apply H3. assumption.
        + intros k [H4 H5]. apply H3. assumption.
    - intros [[H2 H3] H4]. split; try assumption. intros k H5.
      destruct (leqTotal k n) as [H6|H6].
        + apply H4. split; assumption.
        + apply le_trans with n; assumption.
Qed.


(*
Lemma finiteNonEmptyHasSmallest : forall (p:nat -> Prop), Finite p -> 
    (exists (k:nat), p k) -> (exists (k:nat), small p k).
Proof.
    unfold Finite, small. intros p [n H1]. revert n p H1. 
    induction n as [|n IH]; intros p H1 [m H2].
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

