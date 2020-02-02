Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Incl.
Require Import Core.Equal.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.
Require Import Semantics.Compatible.

(* Theorem schema 'comprehensionLEM' expressed in set theory abstract syntax.   *)
(* The formulation is parameterized with respect to a formula P, hence this is  *)
(* not a single theorem, but rather a 'theorem schema'. This formulation is     *)
(* correct provided the variables n m p are distinct.                           *)

Definition comprehensionF (P : Formula) (n m p:nat) : Formula :=
    All n (Exi m (All p (Iff (Elem p m) (And (Elem p n) P)))). 


Lemma evalComprehensionF : LEM -> forall (e:Env) (P: Formula) (n m p:nat),
    m <> n ->
    p <> n ->
    p <> m ->
    eval e (comprehensonF P n m p)
        <->
    forall (x:set), exists (y:set), forall (z:set),
        z :: y <-> z :: x /\ (eval' e p P x).
Proof.

Show.

