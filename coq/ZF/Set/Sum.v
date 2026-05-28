Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

(* The sum of two sets, formed by tagging the left and right components.        *)
Definition sum (a b:U) : U := :{ :0: }: :x: a :\/: :{ :1: }: :x: b.
