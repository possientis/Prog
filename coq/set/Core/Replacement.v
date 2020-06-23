Require Import List.

Require Import Utils.LEM.
Require Import Utils.Filter.

Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Compatible.
Require Import Core.Functional.

(* Axiom schema of replacement assuming LEM for our Coq meta-logic.             *)
Theorem replacememtLEM : forall (p:set -> set -> Prop),
    LEM ->
    compatible2 p ->
    functional p  -> 
    forall (x:set),
        exists (y:set), forall (z:set),
            z :: y <-> exists (u:set), u :: x /\ p u z.
Proof.
   intros p L C F x. 
   remember (fun (z:set) => exists (u:set), u :: x /\ p u z) as q eqn:Eq. 
   remember (toList x) as xs eqn:Ex.

Show.
