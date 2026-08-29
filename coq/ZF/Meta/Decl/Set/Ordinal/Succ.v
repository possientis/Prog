Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition succ : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition env : Env := Env.unions
  [ Env.fromListT
    [ ("succ"%string, succ)]
  ].
