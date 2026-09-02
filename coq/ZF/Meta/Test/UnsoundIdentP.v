Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

(* A schematic proof declaration with one set parameter.                        *)
Definition SelfElem : DeclP :=
  let concl := Elem (Var 0) (Var 0) in
    {| paraP  := [TySet]
    ;  conclP := concl
    ;  bodyP  := HoleP concl
    |}.

(* An environment containing only the schematic proof declaration.              *)
Definition env : Env := Env.singleP (Name.local "SelfElem") SelfElem.

(* The named proof ignores its actual argument in the proved proposition.       *)
Proposition BadIdentP :
  CheckP env [TySet; TySet]
    (IdentP (Name.local "SelfElem") [Var 1])
    (Elem (Var 1) (Var 1)).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckIdentP with (tys := [TySet]) (t := conclP SelfElem).
  1: reflexivity.
  apply CheckTsCons.
  - apply CheckVar. reflexivity.
  - apply CheckTsNil.
Qed.
