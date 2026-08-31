Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Union.

Proposition Union : CheckDeclT (Union.env) Union.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckEx, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckEx, CheckAnd.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckElem; apply CheckVar; reflexivity.
Qed.
