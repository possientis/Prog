Require Import Coq.Lists.List.

Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Ctx : Type := list VarTy.

Definition empty : Ctx := [].

Fixpoint typeOf (G:Ctx) (n:nat) : option VarTy :=
  match G, n with
  | []        , _   => None
  | vty :: _  , 0   => Some vty
  | _   :: H  , S n => typeOf H n
  end.
