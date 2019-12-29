Require Import Core.LEM.
Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Syntax.
Require Import Core.Semantics.
Require Import Core.Environment.

(* Theorem 'emptySet' expressed in set theory abstract syntax.                  *)
Definition emptySetF : Formula := Exi 0 (All 1 (Not (Elem 1 0))).

(* Evaluating emptySetF in any environment 'yields' the theorem emptySet.       *)
Lemma evalEmptySetF : LEM -> forall (e:Env),
    eval e emptySetF <-> exists (x:set), forall (z:set), ~ (z :: x).
Proof.
    intros L e. apply evalExi. assumption.
Qed.
