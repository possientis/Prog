Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.

Definition atrans_sound (atrans:aexp -> aexp) : Prop :=
    forall (a:aexp), aequiv a (atrans a).

Definition btrans_sound (btrans:bexp -> bexp) : Prop :=
    forall (b:bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans:com -> com) : Prop :=
    forall (c:com), cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a:aexp) : aexp :=
    match a with
    | ANum n        => ANum n
    | AKey k        => AKey k
    | APlus a1 a2   =>
        match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2)    => ANum (n1 + n2)
        | (a1', a2')            => APlus a1' a2'
        end
    | AMinus a1 a2   =>
        match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2)    => ANum (n1 - n2)
        | (a1', a2')            => AMinus a1' a2'
        end
    | AMult a1 a2   =>
        match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2)    => ANum (n1 * n2)
        | (a1', a2')            => AMult a1' a2'
        end
    end.

Fixpoint fold_constants_bexp (b:bexp) : bexp :=
    match b with
    | BTrue         => BTrue
    | BFalse        => BFalse
    | BEq a1 a2     =>
        match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2)    => if eqb n1 n2 then BTrue else BFalse 
        | (a1', a2')            => BEq a1' a2'
        end
    | BLe a1 a2     =>
        match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2)    => if leb n1 n2 then BTrue else BFalse 
        | (a1', a2')            => BLe a1' a2'
        end
    | BNot b1       =>
        match (fold_constants_bexp b1) with
        | BTrue     => BFalse
        | BFalse    => BTrue
        | b1'       => BNot b1'
        end
    | BAnd b1 b2     =>
        match (fold_constants_bexp b1, fold_constants_bexp b2) with
        | (BTrue, BTrue)    => BTrue
        | (BTrue, BFalse)   => BFalse
        | (BFalse, BTrue)   => BFalse
        | (BFalse, BFalse)  => BFalse
        | (b1', b2')        => BAnd b1' b2'
        end
    end.


Fixpoint fold_constants_com (c:com) : com :=
    match c with
    | SKIP          => SKIP
    | k ::= a       => k ::= (fold_constants_aexp a)
    | c1 ;; c2      => (fold_constants_com c1) ;; (fold_constants_com c2)
    | CIf b c1 c2   => match (fold_constants_bexp b) with
                       | BTrue      => fold_constants_com c1
                       | BFalse     => fold_constants_com c2
                       | b'         => CIf b' (fold_constants_com c1) 
                                              (fold_constants_com c2)
                       end
    | CWhile b c1   => match (fold_constants_bexp b) with
                       | BTrue     => CWhile BTrue SKIP  (* oo-loop all the same*)
                       | BFalse    => SKIP
                       | b'        => CWhile b' (fold_constants_com c1)
                       end
    end.


