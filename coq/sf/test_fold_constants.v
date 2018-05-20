Require Import nat.
Require Import syntax.
Require Import state.
Require Import fold_constants.


Example fold_aexp1 : fold_constants_aexp
    (AMult (APlus (ANum 1) (ANum 2)) (AKey x)) = AMult (ANum 3) (AKey x).
Proof. reflexivity. Qed.

Example fold_aexp2 : fold_constants_aexp
    (AMinus 
        (AKey x) 
        (APlus 
            (AMult 
                (ANum 0) 
                (ANum 6))
             (AKey y))) =
    (AMinus
        (AKey x)
        (APlus
            (ANum 0)
            (AKey y))).
Proof. reflexivity. Qed.


Example fold_bexp1 : fold_constants_bexp 
    (BAnd BTrue (BNot (BAnd BFalse BTrue))) = BTrue.
Proof. reflexivity. Qed.


Example fold_bexp2 : fold_constants_bexp
    (BAnd (BEq (AKey x) (AKey y))
          (BEq (ANum 0)
               (AMinus (ANum 2) (APlus (ANum 1) (ANum 2))))) =
    BAnd (BEq (AKey x) (AKey y)) BTrue.
Proof. reflexivity. Qed.

Example fold_com1 : fold_constants_com 
    (x ::= APlus (ANum 4) (ANum 5) ;;
     y ::= AMinus (AKey x) (ANum 3);;
     IFB BEq (AMinus (AKey x) (AKey y))
             (APlus (ANum 2) (ANum 4))
     THEN
        SKIP
     ELSE
        y ::= ANum 0
     FI;;
     IFB BLe (ANum 0) 
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
        y ::= ANum 0
     ELSE
        SKIP
     FI;;
     WHILE BEq (AKey y) (ANum 0) DO
        x ::= APlus (AKey x) (ANum 1)
     END)
     =
     (x ::= ANum 9;;
      y ::= AMinus (AKey x) (ANum 3);;
      IFB BEq (AMinus (AKey x) (AKey y)) (ANum 6)
      THEN
        SKIP
      ELSE
        y ::= ANum 0
      FI;;
      y ::= ANum 0;;
      WHILE BEq (AKey y) (ANum 0) DO
        x ::= APlus (AKey x) (ANum 1)
      END).
Proof. reflexivity. Qed.      
    




