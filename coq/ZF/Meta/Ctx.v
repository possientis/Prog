Require Import Coq.Lists.List.

Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Ctx : Type := list Ty.

Definition empty : Ctx := [].

Fixpoint typeOf (G:Ctx) (n:nat) : option Ty :=
  match G, n with
  | []        , _   => None
  | ty  :: _  , 0   => Some ty
  | _   :: H  , S n => typeOf H n
  end.
