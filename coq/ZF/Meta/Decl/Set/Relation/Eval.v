Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Set.Empty.
Require Import ZF.Meta.Decl.Set.Relation.FunctionOn.

Definition eval : DeclT :=
  {| para := [TySet; TySet]
  ;  res  := TySet
  ;  body := HoleT TySet
  |}.

Definition env : Env := Env.unions
  [ Env.fromListT
    [ ("eval"%string, eval)]
  ].


