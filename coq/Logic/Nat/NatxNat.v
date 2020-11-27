Require Import Coq.Arith.Le.
Require Import Coq.Arith.Plus.

Require Import Logic.Class.Ord.
Require Import Logic.Axiom.Dec.
Require Import Logic.Nat.Subset.

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
Definition toNat (x y:nat) : nat := f2 (x + y) y.

Lemma checkToNat_00 : toNat 0 0 = 0. Proof. reflexivity. Qed.
Lemma checkToNat_10 : toNat 1 0 = 1. Proof. reflexivity. Qed.
Lemma checkToNat_01 : toNat 0 1 = 2. Proof. reflexivity. Qed.
Lemma checkToNat_20 : toNat 2 0 = 3. Proof. reflexivity. Qed.
Lemma checkToNat_11 : toNat 1 1 = 4. Proof. reflexivity. Qed.
Lemma checkToNat_02 : toNat 0 2 = 5. Proof. reflexivity. Qed.
Lemma checkToNat_30 : toNat 3 0 = 6. Proof. reflexivity. Qed.
Lemma checkToNat_21 : toNat 2 1 = 7. Proof. reflexivity. Qed.
Lemma checkToNat_12 : toNat 1 2 = 8. Proof. reflexivity. Qed.
Lemma checkToNat_03 : toNat 0 3 = 9. Proof. reflexivity. Qed.

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
      apply le_plus_l.
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






