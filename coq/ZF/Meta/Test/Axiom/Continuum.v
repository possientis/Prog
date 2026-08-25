Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sig.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition sig : Sig := fun name =>
  if String.eqb name "Aleph"   then Some ([]        , TyClass) else
  if String.eqb name "Ordinal" then Some ([TySet]   , TyProp ) else
  if String.eqb name "card"    then Some ([TySet]   , TySet  ) else
  if String.eqb name "power"   then Some ([TySet]   , TySet  ) else
  if String.eqb name "eval"    then Some ([TyClass; TySet], TySet) else
  if String.eqb name "succ"    then Some ([TySet]   , TySet  ) else
  None.

(* forall a, Ordinal a -> card (power (eval Aleph a)) = eval Aleph (succ a)     *)
Definition GCH : Term :=
  All VarTySet
    (Imp
      (Ident "Ordinal" [Var 0])
      (Equal
        (Ident "card"
          [Ident "power"
            [Ident "eval" [Ident "Aleph" []; Var 0]]])
        (Ident "eval" [Ident "Aleph" []; Ident "succ" [Var 0]]))).

(* The generalized-continuum example is a proposition in the local signature.   *)
Proposition HasTy : HasTy sig Ctx.empty GCH TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
    apply HasTysCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTysNil.
  - apply HasTyEqual.
    + apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
      apply HasTysCons.
      * apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
        apply HasTysCons.
        -- apply HasTyIdent with (argTys := [TyClass; TySet]). 1: reflexivity.
           apply HasTysCons.
           ++ apply HasTyIdent with (argTys := []). 1: reflexivity.
              apply HasTysNil.
           ++ apply HasTysCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTysNil.
        -- apply HasTysNil.
      * apply HasTysNil.
    + apply HasTyIdent with (argTys := [TyClass; TySet]). 1: reflexivity.
      apply HasTysCons.
      * apply HasTyIdent with (argTys := []). 1: reflexivity.
        apply HasTysNil.
      * apply HasTysCons.
        -- apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
           apply HasTysCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTysNil.
        -- apply HasTysNil.
Qed.
