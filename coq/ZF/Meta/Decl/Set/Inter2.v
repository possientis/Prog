Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* inter2 a b : U.                                                              *)
Definition inter2 : DeclT :=
  {| paraT := [TySet; TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("inter2"%string, inter2)
  ].

Definition env : Env := Env.union imports exports.
