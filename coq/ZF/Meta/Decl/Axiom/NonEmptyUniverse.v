Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* exists x, True                                                               *)
Definition NonEmptyUniverse : DeclP :=
  let concl :=
    Ex VarTySet Top
  in
    {| paraP  := []
    ;  conclP := concl
    ;  bodyP  := AxiomP concl
    |}.

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListP
  [ ("NonEmptyUniverse"%string, NonEmptyUniverse)
  ].

Definition env : Env := Env.union imports exports.
