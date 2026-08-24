Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ty.

Definition Sig : Type := string -> option (list Ty * Ty).

Definition empty : Sig := fun _ => None.
