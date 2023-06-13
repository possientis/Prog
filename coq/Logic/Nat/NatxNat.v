Require Import Coq.Arith.Le.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Mult.
Import Nat.

Require Import Logic.Class.Ord.
Require Import Logic.Axiom.Dec.

Require Import Logic.Nat.Leq.
Require Import Logic.Nat.Subset.

(* Attempting to prove the existence of a bijection N <-> N x N but giving up   *)
(* for now, as it appears to be more involved than expected.                    *)

(* We want to define a map toNat : NxN -> N such that                           *)
(* toNat 0 0 = 0                                                                *)
(* toNat 1 0 = 1                                                                *)
(* toNat 0 1 = 2                                                                *)
(* toNat 2 0 = 3                                                                *)
(* toNat 1 1 = 4                                                                *)
(* toNat 0 2 = 5    etc.                                                        *)

(* The first step is to carry out the following change of variable:             *)
Definition f0 (x y:nat) : nat * nat := (x + y, y).

(* f0 0 0 = (0,0)                                                               *)
(* f0 1 0 = (1,0)                                                               *)
(* f0 0 1 = (1,1)                                                               *)
(* f0 2 0 = (2,0)                                                               *)
(* f0 1 1 = (2,1)                                                               *)
(* f0 0 2 = (2,2)                                                               *)

Lemma checkf0_00 : f0 0 0 = (0,0). Proof. reflexivity. Qed.
Lemma checkf0_10 : f0 1 0 = (1,0). Proof. reflexivity. Qed.
Lemma checkf0_01 : f0 0 1 = (1,1). Proof. reflexivity. Qed.
Lemma checkf0_20 : f0 2 0 = (2,0). Proof. reflexivity. Qed.
Lemma checkf0_11 : f0 1 1 = (2,1). Proof. reflexivity. Qed.
Lemma checkf0_02 : f0 0 2 = (2,2). Proof. reflexivity. Qed.

(* So we are reduced to the simpler problem of defining a map f2 : NxN -> N:    *)
(* f2 0 0 = 0                                                                   *)
(* f2 1 0 = 1                                                                   *)
(* f2 1 1 = 2                                                                   *)
(* f2 2 0 = 3                                                                   *)
(* f2 2 1 = 4                                                                   *)
(* f2 2 2 = 5       etc.                                                        *)
(* How f2 x y is defined for x < y is irrelevant to us                          *)

(* We first define a function f1 : N -> N representing the values of f2 on the  *)
(* diagonal, i.e. f1 n = f2 n n. We want to have:                               *)
(* f1 0 = 0                                                                     *)
(* f1 1 = 2                                                                     *)
(* f1 2 = 5                                                                     *)
(* f1 3 = 9                                                                     *)
(* f1 4 = 14                                                                    *)
(* f1 5 = 20        etc.                                                        *)

(* f1 n = n * (n + 3)/2                                                         *)
Fixpoint f1 (n:nat) : nat := 
    match n with
    | 0     => 0
    | S n   => f1 n + S (S n)
    end.  

Lemma checkf1_0 : f1 0 = 0.  Proof. reflexivity. Qed.
Lemma checkf1_1 : f1 1 = 2.  Proof. reflexivity. Qed.
Lemma checkf1_2 : f1 2 = 5.  Proof. reflexivity. Qed.
Lemma checkf1_3 : f1 3 = 9.  Proof. reflexivity. Qed.
Lemma checkf1_4 : f1 4 = 14. Proof. reflexivity. Qed.
Lemma checkf1_5 : f1 5 = 20. Proof. reflexivity. Qed.

(* f2 can then be defined using f1                                              *)
Definition f2 (x y:nat) : nat :=
    match x with
    | 0     => f1 y 
    | S x   => f1 x + S y
    end. 

Lemma checkf2_00 : f2 0 0 = 0. Proof. reflexivity. Qed.
Lemma checkf2_10 : f2 1 0 = 1. Proof. reflexivity. Qed.
Lemma checkf2_11 : f2 1 1 = 2. Proof. reflexivity. Qed.
Lemma checkf2_20 : f2 2 0 = 3. Proof. reflexivity. Qed.
Lemma checkf2_21 : f2 2 1 = 4. Proof. reflexivity. Qed.
Lemma checkf2_22 : f2 2 2 = 5. Proof. reflexivity. Qed.
Lemma checkf2_30 : f2 3 0 = 6. Proof. reflexivity. Qed.
Lemma checkf2_31 : f2 3 1 = 7. Proof. reflexivity. Qed.
Lemma checkf2_32 : f2 3 2 = 8. Proof. reflexivity. Qed.
Lemma checkf2_33 : f2 3 3 = 9. Proof. reflexivity. Qed.

(* Our function toNat is simply f2 composed with our change of variable         *)
Definition toNat (p:nat * nat) : nat := 
    match p with
    | (x,y) => f2 (x + y) y
    end.

Lemma checkToNat_00 : toNat (0,0) = 0. Proof. reflexivity. Qed.
Lemma checkToNat_10 : toNat (1,0) = 1. Proof. reflexivity. Qed.
Lemma checkToNat_01 : toNat (0,1) = 2. Proof. reflexivity. Qed.
Lemma checkToNat_20 : toNat (2,0) = 3. Proof. reflexivity. Qed.
Lemma checkToNat_11 : toNat (1,1) = 4. Proof. reflexivity. Qed.
Lemma checkToNat_02 : toNat (0,2) = 5. Proof. reflexivity. Qed.
Lemma checkToNat_30 : toNat (3,0) = 6. Proof. reflexivity. Qed.
Lemma checkToNat_21 : toNat (2,1) = 7. Proof. reflexivity. Qed.
Lemma checkToNat_12 : toNat (1,2) = 8. Proof. reflexivity. Qed.
Lemma checkToNat_03 : toNat (0,3) = 9. Proof. reflexivity. Qed.

Definition A1 (n:nat) : Subset := fun k => n <= f1 k. 

Lemma A1_pDec : forall (n:nat), pDec (A1 n).
Proof.
    intros n k. exact (leqDec n (f1 k)).
Defined.

Lemma A1_notEmpty : forall (n:nat), exists (k:nat), k :: A1 n.
Proof.
    induction n as [|n IH].
    - exists 0. apply le_n.
    - destruct IH as [k H1]. exists (S k). unfold Elem, A1. simpl.
      rewrite <- plus_n_Sm. apply le_n_S. 
      apply le_trans with (f1 k); try assumption.
      apply le_add_r.
Defined.

(* Returns the smallest k such that n <= f1 k                                   *)
Definition f3 (n:nat) : nat := smallestOf (A1 n) (A1_pDec n) (A1_notEmpty n).

Lemma checkf3_0 : f3 0  = 0. Proof. reflexivity. Qed.
Lemma checkf3_1 : f3 1  = 1. Proof. reflexivity. Qed.
Lemma checkf3_2 : f3 2  = 1. Proof. reflexivity. Qed.
Lemma checkf3_3 : f3 3  = 2. Proof. reflexivity. Qed.
Lemma checkf3_4 : f3 4  = 2. Proof. reflexivity. Qed.
Lemma checkf3_5 : f3 5  = 2. Proof. reflexivity. Qed.
Lemma checkf3_6 : f3 6  = 3. Proof. reflexivity. Qed.
Lemma checkf3_7 : f3 7  = 3. Proof. reflexivity. Qed.
Lemma checkf3_8 : f3 8  = 3. Proof. reflexivity. Qed.
Lemma checkf3_9 : f3 9  = 3. Proof. reflexivity. Qed.
Lemma checkf3_10: f3 10 = 4. Proof. reflexivity. Qed.

(* Returns n - m if non-negative, 0 otherwise.                                  *)
Fixpoint sub (n m:nat) : nat :=
    match n with
    | 0     => 0
    | S n   =>
        match m with
        | 0     => S n
        | S m   => sub n m
        end
    end.

Definition f4 (n:nat) : nat*nat :=
    match f3 n with
    | 0     => (0,0)
    | S k   => (S k, sub n (S (f1 k)))
    end.

Lemma checkf4_0 : f4 0  = (0,0). Proof. reflexivity. Qed.
Lemma checkf4_1 : f4 1  = (1,0). Proof. reflexivity. Qed.
Lemma checkf4_2 : f4 2  = (1,1). Proof. reflexivity. Qed.
Lemma checkf4_3 : f4 3  = (2,0). Proof. reflexivity. Qed.
Lemma checkf4_4 : f4 4  = (2,1). Proof. reflexivity. Qed.
Lemma checkf4_5 : f4 5  = (2,2). Proof. reflexivity. Qed.
Lemma checkf4_6 : f4 6  = (3,0). Proof. reflexivity. Qed.
Lemma checkf4_7 : f4 7  = (3,1). Proof. reflexivity. Qed.
Lemma checkf4_8 : f4 8  = (3,2). Proof. reflexivity. Qed.
Lemma checkf4_9 : f4 9  = (3,3). Proof. reflexivity. Qed.
Lemma checkf4_10: f4 10 = (4,0). Proof. reflexivity. Qed.


Definition fromNat (n:nat) : nat * nat :=
    match f4 n with
    | (x,y) => (sub x y, y)
    end.

Lemma checkFromNat_0 : fromNat 0  = (0,0). Proof. reflexivity. Qed.
Lemma checkFromNat_1 : fromNat 1  = (1,0). Proof. reflexivity. Qed.
Lemma checkFromNat_2 : fromNat 2  = (0,1). Proof. reflexivity. Qed.
Lemma checkFromNat_3 : fromNat 3  = (2,0). Proof. reflexivity. Qed.
Lemma checkFromNat_4 : fromNat 4  = (1,1). Proof. reflexivity. Qed.
Lemma checkFromNat_5 : fromNat 5  = (0,2). Proof. reflexivity. Qed.
Lemma checkFromNat_6 : fromNat 6  = (3,0). Proof. reflexivity. Qed.
Lemma checkFromNat_7 : fromNat 7  = (2,1). Proof. reflexivity. Qed.
Lemma checkFromNat_8 : fromNat 8  = (1,2). Proof. reflexivity. Qed.
Lemma checkFromNat_9 : fromNat 9  = (0,3). Proof. reflexivity. Qed.
Lemma checkFromNat_10: fromNat 10 = (4,0). Proof. reflexivity. Qed.

Lemma checkToFrom_0 : toNat (fromNat 0) = 0. Proof. reflexivity. Qed.
Lemma checkToFrom_1 : toNat (fromNat 1) = 1. Proof. reflexivity. Qed.
Lemma checkToFrom_2 : toNat (fromNat 2) = 2. Proof. reflexivity. Qed.
Lemma checkToFrom_3 : toNat (fromNat 3) = 3. Proof. reflexivity. Qed.
Lemma checkToFrom_4 : toNat (fromNat 4) = 4. Proof. reflexivity. Qed.
Lemma checkToFrom_5 : toNat (fromNat 5) = 5. Proof. reflexivity. Qed.
Lemma checkToFrom_6 : toNat (fromNat 6) = 6. Proof. reflexivity. Qed.
Lemma checkToFrom_7 : toNat (fromNat 7) = 7. Proof. reflexivity. Qed.
Lemma checkToFrom_8 : toNat (fromNat 8) = 8. Proof. reflexivity. Qed.
Lemma checkToFrom_9 : toNat (fromNat 9) = 9. Proof. reflexivity. Qed.

Lemma checkFromTo_00 : fromNat (toNat (0,0)) = (0,0). Proof. reflexivity. Qed.
Lemma checkFromTo_10 : fromNat (toNat (1,0)) = (1,0). Proof. reflexivity. Qed.
Lemma checkFromTo_01 : fromNat (toNat (0,1)) = (0,1). Proof. reflexivity. Qed.
Lemma checkFromTo_20 : fromNat (toNat (2,0)) = (2,0). Proof. reflexivity. Qed.
Lemma checkFromTo_11 : fromNat (toNat (1,1)) = (1,1). Proof. reflexivity. Qed.
Lemma checkFromTo_02 : fromNat (toNat (0,2)) = (0,2). Proof. reflexivity. Qed.
Lemma checkFromTo_30 : fromNat (toNat (3,0)) = (3,0). Proof. reflexivity. Qed.
Lemma checkFromTo_21 : fromNat (toNat (2,1)) = (2,1). Proof. reflexivity. Qed.
Lemma checkFromTo_12 : fromNat (toNat (1,2)) = (1,2). Proof. reflexivity. Qed.
Lemma checkFromTo_03 : fromNat (toNat (0,3)) = (0,3). Proof. reflexivity. Qed.


(* returns n * (n + 1)/2                                                        *)
Fixpoint f5 (n:nat) : nat :=
    match n with
    | 0     => 0
    | S n   => f5 n + S n
    end.

Lemma f5_S : forall (n:nat), f5 (S n) = f5 n + S n.
Proof.
    intros n. reflexivity.
Qed.

(* A real proof of correctness rather than testing 10 values...                 *)
Lemma checkf5 : forall (n:nat), 2 * f5 n = n * S n.
Proof.
    induction n as [|n IH].
    - reflexivity.
    - rewrite f5_S. rewrite mul_add_distr_l, IH, <- mul_add_distr_r.
      rewrite mul_comm. assert (n + 2 = S (S n)) as H1.
        { rewrite <- plus_n_Sm, <- plus_n_Sm, <- plus_n_O. reflexivity. }
      rewrite H1. reflexivity.
Qed.

(* Same as toNat                                                                *)
Definition f6 (p:nat * nat) : nat :=
    match p with
    | (x,y) => f5 (x + y) + y
    end.

Lemma checkf6_00 : f6 (0,0) = 0. Proof. reflexivity. Qed.
Lemma checkf6_10 : f6 (1,0) = 1. Proof. reflexivity. Qed.
Lemma checkf6_01 : f6 (0,1) = 2. Proof. reflexivity. Qed.
Lemma checkf6_20 : f6 (2,0) = 3. Proof. reflexivity. Qed.
Lemma checkf6_11 : f6 (1,1) = 4. Proof. reflexivity. Qed.
Lemma checkf6_02 : f6 (0,2) = 5. Proof. reflexivity. Qed.
Lemma checkf6_30 : f6 (3,0) = 6. Proof. reflexivity. Qed.
Lemma checkf6_21 : f6 (2,1) = 7. Proof. reflexivity. Qed.
Lemma checkf6_12 : f6 (1,2) = 8. Proof. reflexivity. Qed.
Lemma checkf6_03 : f6 (0,3) = 9. Proof. reflexivity. Qed.
