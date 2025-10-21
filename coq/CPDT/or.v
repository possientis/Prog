Inductive Either (a b : Type) : Type :=
| Left  : a -> Either a b
| Right : b -> Either a b
.

(* Print or. *)

Arguments Left  {a} {b} _.
Arguments Right {a} {b} _.

(*
Inductive or (A B : Prop) : Prop :=
| or_introl : A -> A \/ B
| or_intror : B -> A \/ B
*)

(* this conversion is possible *)
Definition toOr (A B:Prop) (p:Either A B) : or A B :=
    match p with
    | Left  x   => or_introl x
    | Right y   => or_intror y
    end.

(* but this one is not:
Incorrect elimination of "p" in the inductive type "or":
the return type has sort "Set" while it should be "Prop".
Elimination of an inductive object of sort Prop
is not allowed on a predicate in sort Set
because proofs can be eliminated only to build proofs.

Definition toEither (A B:Prop) (p:or A B) : Either A B :=
        match p with
        | or_introl x   => Left  x
        | or_intror y   => Right y
        end.
*)



