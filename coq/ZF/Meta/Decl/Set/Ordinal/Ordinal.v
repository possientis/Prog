Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Ordinal : DeclT :=
  {| para := [TySet]
  ;  res  := TyProp
  ;  body := HoleT TyProp
  |}.

Definition env : Env := Env.unions
  [ Env.fromListT
    [ ("Ordinal"%string, Ordinal)]
  ].
