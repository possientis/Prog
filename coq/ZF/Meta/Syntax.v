Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive Term : Type :=
| Bot     : Term
| Top     : Term
| Var     : nat    -> Term
| HoleT   : Ty     -> Term
| IdentT  : string -> list Term -> Term
| Elem    : Term   -> Term      -> Term
| Leq     : Term   -> Term      -> Term
| Geq     : Term   -> Term      -> Term
| Lt      : Term   -> Term      -> Term
| Gt      : Term   -> Term      -> Term
| Equal   : Term   -> Term      -> Term
| NotEq   : Term   -> Term      -> Term
| Imp     : Term   -> Term      -> Term
| Iff     : Term   -> Term      -> Term
| And     : Term   -> Term      -> Term
| Or      : Term   -> Term      -> Term
| Not     : Term   -> Term
| All     : VarTy  -> Term      -> Term
| Ex      : VarTy  -> Term      -> Term
| Lam     : Term   -> Term
| App     : Term   -> Term      -> Term
| Def     : Term   -> Proof     -> Proof     -> Term
with Proof : Type :=
| HoleP  : Term    -> Proof
| IdentP : string  -> list Term -> Proof
.
