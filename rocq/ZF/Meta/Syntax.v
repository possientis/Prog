Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Inductive Term : Type :=
(* Logical constants.                                                           *)
| Bot     : Term
| Top     : Term
(* Local variables and typed incomplete terms.                                  *)
| Var     : nat    -> Term
| HoleT   : Ty     -> Term
(* A named term declaration applied to all its ordinary arguments.              *)
| IdentT  : Name   -> list Term -> Term
(* Set-theoretic atomic propositions and comparison forms.                      *)
| Elem    : Term   -> Term      -> Term
| Leq     : Term   -> Term      -> Term
| Geq     : Term   -> Term      -> Term
| Lt      : Term   -> Term      -> Term
| Gt      : Term   -> Term      -> Term
| Equal   : Term   -> Term      -> Term
| NotEq   : Term   -> Term      -> Term
(* Propositional connectives.                                                   *)
| Imp     : Term   -> Term      -> Term
| Iff     : Term   -> Term      -> Term
| And     : Term   -> Term      -> Term
| Or      : Term   -> Term      -> Term
| Not     : Term   -> Term
(* Quantifiers bind one set variable.                                           *)
| All     : Term   -> Term
| Ex      : Term   -> Term
(* A class abstraction binds one set variable.                                  *)
| Lam     : Term   -> Term
(* Class application forms a proposition.                                       *)
| App     : Term   -> Term      -> Term
(* A definition term packages a class with existence and uniqueness proofs.     *)
| Def     : Term   -> Proof     -> Proof     -> Term
with Proof : Type :=
(* An incomplete proof reference for a proposition.                             *)
| HoleP  : Term    -> Proof
(* An axiomatic proof reference for a proposition.                              *)
| AxiomP : Term    -> Proof
(* A named proof declaration applied to all its ordinary arguments.             *)
| IdentP : Name    -> list Term -> Proof
.
