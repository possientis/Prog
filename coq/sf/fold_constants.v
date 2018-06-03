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

Definition fold_constants_bexp:= btrans fold_constants_aexp.
Definition fold_constants_com := ctrans fold_constants_aexp fold_constants_bexp.





