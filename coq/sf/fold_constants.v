Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.
Require Import transform.

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

Definition fold_constants_com := ctrans fold_constants_aexp fold_constants_bexp.

Lemma fold_constants_bexp_is_btrans : forall (b:bexp),
    fold_constants_bexp b = btrans fold_constants_aexp b.
Proof.
    intros b. induction b; try (reflexivity). 
    - simpl. rewrite IHb. reflexivity.
    - simpl. rewrite IHb1, IHb2. reflexivity.
Qed.





