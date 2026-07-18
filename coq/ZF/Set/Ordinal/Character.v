Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.

(* The character of cofinality of the ordinal a.                                *)
Definition charac (a:U) : U := inf {{ x :< succ a | Cofinal a }}.
