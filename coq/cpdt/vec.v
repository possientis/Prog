Require Import List.
Import ListNotations.

Inductive Vec (a:Type) : nat -> Type :=
| Nil  : Vec a 0
| Cons : forall (n:nat), a -> Vec a n -> Vec a (S n)
.

Arguments Nil  {a}.
Arguments Cons {a} {n}.

   
Fixpoint append (a:Type) (n m:nat) (xs:Vec a n) (ys:Vec a m) : Vec a (n + m) :=
    match xs with
    | Nil       => ys
    | Cons x xs => Cons x (append _ _ _ xs ys) 
    end.

Arguments append {a} {n} {m}.

Fixpoint inject (a:Type) (xs:list a) : Vec a (length xs) :=
    match xs with
    | nil       => Nil
    | x :: xs   => Cons x (inject a xs)
    end.

Arguments inject {a}.

(*
Compute inject [1;2;3].
*)

Fixpoint unject (a:Type) (n:nat) (xs:Vec a n) : list a :=
    match xs with
    | Nil       => nil
    | Cons x xs => x :: unject _ _ xs
    end.

Arguments unject {a} {n}.

