Require Import term.

Definition value (t:Term) : Prop :=
    match t with
    | VarTerm _     => False
    | AbsTerm _ _   => True
    | AppTerm _ _   => False
    | TAbsTerm _ _  => True
    | TAppTerm _ _  => False
    end.
