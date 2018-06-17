Require Import term.

Definition isValue (t:Term) : bool :=
    match t with
    | VarTerm _     => false
    | AbsTerm _ _   => true
    | AppTerm _ _   => false
    | TAbsTerm _ _  => true
    | TAppTerm _ _  => false
    end.
