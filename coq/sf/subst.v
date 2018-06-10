Require Import syntax.
Require Import dictionary.

Fixpoint subst_aexp (k:Key)(u:aexp)(a:aexp) : aexp :=
    match a with
    | ANum n        => ANum n
    | AKey k'       => if beq_Key k k' then u else AKey k'
    | APlus  a1 a2  => APlus  (subst_aexp k u a1) (subst_aexp k u a2)
    | AMinus a1 a2  => AMinus (subst_aexp k u a1) (subst_aexp k u a2)
    | AMult  a1 a2  => AMult  (subst_aexp k u a1) (subst_aexp k u a2)
    end.



