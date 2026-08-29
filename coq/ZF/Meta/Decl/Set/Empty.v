Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition empty : DeclT :=
  {| paraT := [];
     resT  := TySet;
     bodyT := HoleT TySet |}.

Definition env : Env := Env.unions
  [ Env.fromListT
    [ ("empty"%string  , empty)]
  ].


