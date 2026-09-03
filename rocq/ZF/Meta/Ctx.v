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

(* A lookup remains valid after adding newer variables in front.                *)
Proposition TypeOfAppR :
  forall (G D:Ctx) (n:nat) (ty:Ty),
    typeOf D n = Some ty ->
    typeOf (G ++ D) (length G + n) = Some ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G D n ty H1.
  induction G as [|ty' G IH]; assumption.
Qed.
