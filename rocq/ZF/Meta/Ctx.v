Require Import Coq.Lists.List.

Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Ctx : Type := list Ty.

Definition empty : Ctx := [].
