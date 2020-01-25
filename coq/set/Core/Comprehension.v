Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Filter.
Require Import Core.ToList.
Require Import Core.Compatible.

(* Given a set x and a decidable predicate p, creates a set made of all those   *)
(* elements of x which satisfy the predicate p.                                 *)
Definition comp (x:set)(p:set -> Prop)(q:Dec p) : set :=
    fromList (filter q (toList x)).

(*
(* The predicate needs to be decidable and compatible.                          *)
Lemma compCharac : forall (x:set) (p:set -> Prop) (q:Dec p), compatible p ->
    forall (z:set), z :: comp x p q <-> z :: x /\ p x.
Proof.

Show.
    
*)

