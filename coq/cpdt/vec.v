Require Import List.
Import ListNotations.

Inductive Fin : nat -> Set :=
| First : forall (n:nat), Fin (S n)
| Next  : forall (n:nat), Fin n -> Fin (S n)
.

Arguments Next  {n}.
Arguments First {n}.

Definition x0 : Fin 3 := First.
Definition x1 : Fin 3 := Next First.
Definition x2 : Fin 3 := Next (Next First).


Inductive Vect (a:Type) : nat -> Type :=
| Nil  : Vect a 0
| Cons : forall (n:nat), a -> Vect a n -> Vect a (S n)
.

Arguments Nil {a}.
Arguments Cons {a} {n}.

Fixpoint append (a:Type) (n m:nat) (xs:Vect a n) (ys:Vect a m) : Vect a (n + m) :=
    match xs with
    | Nil       => ys
    | Cons x xs => Cons x (append _ _ _ xs ys) 
    end.

Arguments append {a} {n} {m}.

Fixpoint inject (a:Type) (xs:list a) : Vect a (length xs) :=
    match xs with
    | nil       => Nil
    | x :: xs   => Cons x (inject a xs)
    end.

Arguments inject {a}.

(*
Compute inject [1;2;3].
*)


Fixpoint unject (a:Type) (n:nat) (xs:Vect a n) : list a :=
    match xs with
    | Nil       => nil
    | Cons x xs => x :: unject _ _ xs
    end.

Arguments unject {a} {n}.

Definition head (a:Type) (n:nat) (xs:Vect a (S n)) : a :=
    match xs in Vect _ (S n) with
    | Cons x _  => x
    end.

Arguments head {a} {n}.

(*
Compute head (inject [1;2;3]).
*)

Fixpoint get (a:Type) (n:nat) (xs:Vect a n) : Fin n -> a :=
    match xs with
    | Nil   => fun i =>             (* Fin 0 is an empty type           *)
        match i in Fin n' return (  (* n' being 0 can never happen      *) 
            match n' with
            | 0     => a            (* but n' has to be 0 so typechecks *)
            | S _   => unit         (* now this type has a value        *)
            end) with
        | First     => tt           (* which we can return              *) 
        | Next _    => tt
        end
    | Cons x ys   => fun i =>
        match i in Fin n' return Vect a (pred n') -> a with
        | First     => fun _  => x
        | Next  i'  => fun zs => get _ _ zs i'
        end ys
    end.

Arguments get {a} {n}.

Definition v3 : Vect nat 3 := Cons 1 (Cons 2 (Cons 3 Nil)).
Definition v4 : Vect nat 4 := Cons 4 (Cons 3 (Cons 2 (Cons 1 Nil))).

(*
(* very very nice *)
Compute get v3 First.                   (* 1 *)
Compute get v3 (Next First).            (* 2 *)
Compute get v3 (Next (Next First)).     (* 3 *)
Compute get v4 First.                   (* 4 *)
*)

Fixpoint vmap (a b:Type) (n:nat) (f:a -> b) (xs:Vect a n) : Vect b n :=
    match xs with 
    | Nil       => Nil
    | Cons x xs => Cons (f x) (vmap _ _ _ f xs)
    end.

Arguments vmap {a} {b} {n}.

(* Can't do this proof with current tooling, won't use 'dep_destruct'           *)
(*
Lemma get_vmap : forall (a b:Type) (n:nat) (f:a -> b) (xs:Vect a n) (i:Fin n),
    get (vmap f xs) i = f (get xs i).
Proof.
    intros a b n f. revert n. induction xs as [|n x xs IH].
    - admit.
    - intros i. 


Show.
*)


