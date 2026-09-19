Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Classic.

(* Double negation is a well-typed proof declaration.                           *)
Proposition DoubleNegation : CheckP (Classic.env) DoubleNegation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold DoubleNegation. checkP.
Qed.

(* Negated universality is a well-typed proof declaration.                      *)
Proposition NotForAll : CheckP (Classic.env) NotForAll.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotForAll. checkP.
Qed.

(* Negated universal negation is a well-typed proof declaration.                *)
Proposition NotForAllNot : CheckP (Classic.env) NotForAllNot.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold NotForAllNot. checkP.
Qed.

(* The law of excluded middle is a well-typed proof declaration.                *)
Proposition LawExcludedMiddle : CheckP (Classic.env) LawExcludedMiddle.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold LawExcludedMiddle. checkP.
Qed.
