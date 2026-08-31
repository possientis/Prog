Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Power.

Proposition Power : CheckDeclT (Power.env) Power.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckEx, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckLeq; apply CheckVar; reflexivity.
Qed.
