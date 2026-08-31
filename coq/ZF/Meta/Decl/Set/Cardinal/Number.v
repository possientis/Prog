Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* card a : U.                                                                  *)
Definition card : DeclT :=
  {| paraT := [TySet]
  ;  resT  := TySet
  ;  bodyT := HoleT TySet
  |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("card"%string, card)
  ].

Definition env : Env := Env.union imports exports.
