Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.NonEmptyUniverse.

Proposition NonEmptyUniverse :
  CheckDeclT (NonEmptyUniverse.env) NonEmptyUniverse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckEx, CheckTop.
Qed.
