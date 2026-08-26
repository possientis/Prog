Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Signature.

Definition Sigs : Type := string -> option Signature.

Definition empty : Sigs := fun _ => None.
