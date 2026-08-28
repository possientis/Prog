Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Aleph : Decl :=
  {| para := [];
     res  := TyClass;
     body := None |}.

Definition Ordinal : Decl :=
  {| para := [TySet];
     res  := TyProp;
     body := None |}.

Definition card : Decl :=
  {| para := [TySet];
     res  := TySet;
     body := None |}.

Definition power : Decl :=
  {| para := [TySet];
     res  := TySet;
     body := None |}.

Definition eval : Decl :=
  {| para := [TyClass; TySet];
     res  := TySet;
     body := None |}.

Definition succ : Decl :=
  {| para := [TySet];
     res  := TySet;
     body := None |}.

Definition env : Env := fun name =>
  if String.eqb name "Aleph"   then Some Aleph else
  if String.eqb name "Ordinal" then Some Ordinal else
  if String.eqb name "card"    then Some card else
  if String.eqb name "power"   then Some power else
  if String.eqb name "eval"    then Some eval else
  if String.eqb name "succ"    then Some succ else
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

(* The generalized-continuum example is a proposition in the local environment. *)
Proposition HasTy : HasTyIn env Ctx.empty GCH TyProp.
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
