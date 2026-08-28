Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.HasTy.
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

Definition env : Env := Env.fromListT
  [ ("Aleph"%string  , Aleph)
  ; ("Ordinal"%string, Ordinal)
  ; ("card"%string   , card)
  ; ("power"%string  , power)
  ; ("eval"%string   , eval)
  ; ("succ"%string   , succ)
  ].

(* forall a, Ordinal a -> card (power (eval Aleph a)) = eval Aleph (succ a)     *)
Definition GCH : Term :=
  All VarTySet
    (Imp
      (IdentT "Ordinal" [Var 0])
      (Equal
        (IdentT "card"
          [IdentT "power"
            [IdentT "eval" [IdentT "Aleph" []; Var 0]]])
        (IdentT "eval" [IdentT "Aleph" []; IdentT "succ" [Var 0]]))).

(* The generalized-continuum example is a proposition in the local environment. *)
Proposition HasTy : HasTyT env Ctx.empty GCH TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyIdentT with (d:=Ordinal). 1: reflexivity.
    apply HasTyTsCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyTsNil.
  - apply HasTyEqual.
    + apply HasTyIdentT with (d:=card). 1: reflexivity.
      apply HasTyTsCons.
      * apply HasTyIdentT with (d:=power). 1: reflexivity.
        apply HasTyTsCons.
        -- apply HasTyIdentT with (d:=eval). 1: reflexivity.
           apply HasTyTsCons.
           ++ apply HasTyIdentT with (d:=Aleph). 1: reflexivity.
              apply HasTyTsNil.
           ++ apply HasTyTsCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTyTsNil.
        -- apply HasTyTsNil.
      * apply HasTyTsNil.
    + apply HasTyIdentT with (d:=eval). 1: reflexivity.
      apply HasTyTsCons.
      * apply HasTyIdentT with (d:=Aleph). 1: reflexivity.
        apply HasTyTsNil.
      * apply HasTyTsCons.
        -- apply HasTyIdentT with (d:=succ). 1: reflexivity.
           apply HasTyTsCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTyTsNil.
        -- apply HasTyTsNil.
Qed.
