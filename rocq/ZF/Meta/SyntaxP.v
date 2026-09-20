Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxT.

Inductive Proof : Type :=
(* An incomplete proof reference for a proposition.                             *)
| HoleP  : Term    -> Proof
(* An axiomatic proof reference for a proposition.                              *)
| AxiomP : Term    -> Proof
(* A named proof declaration applied to all its ordinary arguments.             *)
| IdentP : Name    -> Terms -> Proof
.
