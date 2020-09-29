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

Fixpoint f1 (n:nat) : nat := 
    match n with
    | 0     => 0
    | S n   => f1 n + S (S n)
    end.  

(* f2 can then be defined using f1                                              *)
Definition f2 (x y:nat) : nat :=
    match x with
    | 0     => f1 y 
    | S x   => f1 x + S y
    end. 

(* Our function toNat is simply f2 composed with our change of variable         *)
Definition toNat (x y:nat) : nat := f2 (x + y) y.

Lemma checkToNat00 : toNat 0 0 = 0. Proof. reflexivity. Qed.
Lemma checkToNat10 : toNat 1 0 = 1. Proof. reflexivity. Qed.
Lemma checkToNat01 : toNat 0 1 = 2. Proof. reflexivity. Qed.
Lemma checkToNat20 : toNat 2 0 = 3. Proof. reflexivity. Qed.
Lemma checkToNat11 : toNat 1 1 = 4. Proof. reflexivity. Qed.
Lemma checkToNat02 : toNat 0 2 = 5. Proof. reflexivity. Qed.
Lemma checkToNat30 : toNat 3 0 = 6. Proof. reflexivity. Qed.
Lemma checkToNat21 : toNat 2 1 = 7. Proof. reflexivity. Qed.
Lemma checkToNat12 : toNat 1 2 = 8. Proof. reflexivity. Qed.
Lemma checkToNat03 : toNat 0 3 = 9. Proof. reflexivity. Qed.




