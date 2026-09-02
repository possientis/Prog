Require Import List.
Import ListNotations.

Require Import eq.

Fixpoint index (v:Type) (p:Eq v) (x:v) (l:list v) : option nat :=
    match l with
    | []                => None
    | (y :: l)          => 
        match (p x y) with
        | left _        => Some 0
        | right _       => 
            match index v p x l with
            | None      => None
            | Some n    => Some (S n)
            end
        end
    end.

Arguments index {v} _ _ _. 


