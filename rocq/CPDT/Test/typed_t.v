Require Import Bool.
Require Import List.
Require Import Arith.

Require Import typed.
Require Import Utils.nat.


Lemma blt_nat_test1: blt_nat 0 0 = false.
Proof. reflexivity. Qed.

Lemma blt_nat_test2: blt_nat 1 0 = false.
Proof. reflexivity. Qed.

Lemma blt_nat_test3: blt_nat 0 1 = true.
Proof. reflexivity. Qed.

Lemma blt_nat_test4: blt_nat 1 1 = false.
Proof. reflexivity. Qed.

Lemma typeDenote_test1: typeDenote Nat = nat.
Proof. reflexivity. Qed.

Lemma typeDenote_test2: typeDenote Bool = bool.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test1: tbinopDenote TPlus = plus.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test2: tbinopDenote TTimes = mult.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test3: tbinopDenote (TEq Nat) = Nat.eqb.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test4: tbinopDenote (TEq Bool) = eqb.
Proof. reflexivity. Qed.

Lemma tbinopDenote_test5: tbinopDenote TLt = blt_nat.
Proof. reflexivity. Qed.

Lemma texpDenote_test1: texpDenote (TNConst 42) = 42.
Proof. reflexivity. Qed.

Lemma texpDenote_test2: texpDenote (TBConst true) = true.
Proof. reflexivity. Qed.

Lemma texpDenote_test3: texpDenote (TBConst false) = false.
Proof. reflexivity. Qed.

Lemma texpDenote_test4: texpDenote 
    ( TBinop TTimes 
        (TBinop TPlus (TNConst 2)(TNConst 3)) 
        (TNConst 7)) = 35.
Proof. reflexivity. Qed.

Lemma texpDenote_test5: texpDenote 
    ( TBinop (TEq Nat) 
        (TBinop TPlus (TNConst 4) (TNConst 3))
        (TNConst 7)) = true.
Proof. reflexivity. Qed.

Lemma texpDenote_test6: texpDenote 
    ( TBinop (TEq Bool) 
        (TBinop (TEq Nat) (TNConst 2) (TNConst 3))
        (TBConst false)) = true.
Proof. reflexivity. Qed.

Lemma texpDenote_test7: texpDenote 
    ( TBinop TLt
        (TBinop TPlus (TNConst 2) (TNConst 3))
        (TNConst 7)) = true.
Proof. reflexivity. Qed.


Definition x : unit := tt.

(*
Print tcompile.
*)

Lemma tcompile_test1: 
    tprogDenote (tcompile (TNConst 42) nil) tt = (42,tt). 
Proof. reflexivity. Qed.

Lemma tcompile_test2: 
    tprogDenote (tcompile (TBConst true) nil) tt = (true,tt). 
Proof. reflexivity. Qed.
 
Lemma tcompile_test3: 
    tprogDenote (tcompile (TBConst false) nil) tt = (false,tt). 
Proof. reflexivity. Qed.

Lemma tcompile_test4:
    tprogDenote 
        (tcompile 
            (TBinop TTimes 
                (TBinop TPlus (TNConst 2) (TNConst 3))
                (TNConst 7)) nil) tt = (35,tt).
Proof. reflexivity. Qed.

Lemma tcompile_test5:
    tprogDenote
        (tcompile
            (TBinop (TEq Nat)
                (TBinop TPlus (TNConst 2) (TNConst 3))
                (TNConst 7)) nil) tt = (false, tt).
Proof. reflexivity. Qed.

Lemma tcompile_test6:
    tprogDenote
        (tcompile
            (TBinop (TEq Nat)
                (TBinop TPlus (TNConst 2) (TNConst 3))
                (TNConst 5)) nil) tt = (true, tt).
Proof. reflexivity. Qed.


Lemma tcompile_test7:
    tprogDenote
        (tcompile
            (TBinop (TEq Bool)
                (TBinop (TEq Nat) (TNConst 2) (TNConst 2))
                (TBConst true)) nil) tt = (true, tt).
Proof. reflexivity. Qed.

Lemma tcompile_test8:
    tprogDenote
        (tcompile
            (TBinop (TEq Bool)
                (TBinop (TEq Nat) (TNConst 3) (TNConst 2))
                (TBConst true)) nil) tt = (false, tt).
Proof. reflexivity. Qed.


Lemma tcompile_test9:
    tprogDenote
        (tcompile
            (TBinop TLt
                (TBinop TPlus (TNConst 2) (TNConst 3))
                (TNConst 5)) nil) tt = (false, tt).
Proof. reflexivity. Qed.

Lemma tcompile_test10:
    tprogDenote
        (tcompile
            (TBinop TLt
                (TBinop TPlus (TNConst 2) (TNConst 3))
                (TNConst 6)) nil) tt = (true, tt).
Proof. reflexivity. Qed.

(*
Extraction Language Haskell.
Extraction tcompile.
*)






