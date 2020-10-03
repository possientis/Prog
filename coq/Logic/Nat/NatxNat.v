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


