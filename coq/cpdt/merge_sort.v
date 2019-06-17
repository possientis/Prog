Require Import List.

Fixpoint insert (a:Type) (le:a -> a -> bool) (x:a) (xs:list a) : list a :=
    match xs with
    | nil       => x :: nil
    | (y :: ys) => if le x y
        then x :: xs
        else y :: insert a le x ys
    end.

Arguments insert {a} _ _ _.

Fixpoint merge (a:Type) (le:a -> a -> bool) (xs ys:list a) : list a :=
    match xs with
    | nil       => ys
    | (x :: xs) => insert le x (merge a le xs ys)
    end. 

Arguments merge {a} _ _ _.
