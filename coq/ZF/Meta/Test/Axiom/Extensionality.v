Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Extensionality.

Proposition Extensionality : CheckDeclT (Extensionality.env) Extensionality.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckImp.
  - apply CheckAll, CheckIff.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckEqual;  apply CheckVar; reflexivity.
Qed.
