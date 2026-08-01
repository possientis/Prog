Require Import ZF.Class.Equiv.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Character.
Require Import ZF.Set.Ordinal.Omega.

(* The set a is a regular cardinal.                                             *)
Definition Regular (a:U) : Prop := InfiniteCard a /\ charac a = a.

(* Omega is a regular cardinal.                                                 *)
Proposition WhenOmega : Regular :N.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  split.
  - apply InfiniteCard.HasOmega.
  - apply Character.WhenOmega.
Qed.
