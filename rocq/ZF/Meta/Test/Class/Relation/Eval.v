Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.Eval.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class-relation evaluation is well sorted.           *)
Proposition eval : CheckT (Eval.env) Eval.eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.eval. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of class-relation evaluation with equivalence is well sorted.  *)
Proposition EquivCompat : CheckP (Eval.env) Eval.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.EquivCompat. checkP.
Qed.

(* The value-present evaluation characterization is well sorted.                *)
Proposition WhenHasValueAt : CheckP (Eval.env) Eval.WhenHasValueAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.WhenHasValueAt. checkP.
Qed.

(* The functional-at-point evaluation characterization is well sorted.          *)
Proposition WhenFunctionalAt : CheckP (Eval.env) Eval.WhenFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.WhenFunctionalAt. checkP.
Qed.

(* The functional evaluation characterization is well sorted.                   *)
Proposition WhenFunctional : CheckP (Eval.env) Eval.WhenFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.WhenFunctional. checkP.
Qed.

(* Evaluation at a point without a value is well sorted.                        *)
Proposition WhenNotHasValueAt : CheckP (Eval.env) Eval.WhenNotHasValueAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.WhenNotHasValueAt. checkP.
Qed.

(* Evaluation at a non-functional point is well sorted.                         *)
Proposition WhenNotFunctionalAt : CheckP (Eval.env) Eval.WhenNotFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.WhenNotFunctionalAt. checkP.
Qed.

(* Evaluation outside the domain is well sorted.                                *)
Proposition WhenNotInDomain : CheckP (Eval.env) Eval.WhenNotInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.WhenNotInDomain. checkP.
Qed.

(* Smallness of class-relation evaluation is well sorted.                       *)
Proposition IsSmall : CheckP (Eval.env) Eval.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Eval.IsSmall. checkP.
Qed.
