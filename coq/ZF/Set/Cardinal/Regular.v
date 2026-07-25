Require Import ZF.Class.Equiv.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Character.

(* The set a is a regular cardinal.                                             *)
Definition Regular (a:U) : Prop := InfiniteCard a /\ charac a = a.
