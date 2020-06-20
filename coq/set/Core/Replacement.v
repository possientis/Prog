Require Import List.

Require Import Utils.LEM.
Require Import Utils.Filter.

Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Compatible.
Require Import Core.Functional.

(* Axiom schema of replacement assuming LEM for our Coq meta-logic.             *)
Theorem replacememtLEM : LEM -> forall (p:set -> set -> set -> Prop),
    compatible3 p    -> forall (x:set), 
    functional (p x) -> exists (y:set), forall (z:set),
        z :: y <-> exists (u:set), u :: x /\ p x u z.
Proof.
   intros L p C x F. 
   remember (fun (z:set) => exists (u:set), u :: x /\ p x u z) as q eqn:Eq. 
   remember (toList x) as xs eqn:Ex.

Show.
