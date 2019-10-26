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



