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

Require Import ZF.Meta.Decl.Set.Relation.EvalOfClass.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class relation evaluation as a set is well sorted.  *)
Proposition eval : CheckT (EvalOfClass.env) EvalOfClass.eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.eval. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of set-valued class evaluation is well sorted.                 *)
Proposition EquivCompat : CheckP (EvalOfClass.env) EvalOfClass.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.EquivCompat. checkP.
Qed.

(* The value-present evaluation characterization is well sorted.                *)
Proposition HasValueAtEvalCharac :
  CheckP (EvalOfClass.env) EvalOfClass.HasValueAtEvalCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.HasValueAtEvalCharac. checkP.
Qed.

(* The value-present satisfaction theorem is well sorted.                       *)
Proposition HasValueAtSatisfies :
  CheckP (EvalOfClass.env) EvalOfClass.HasValueAtSatisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.HasValueAtSatisfies. checkP.
Qed.

(* The functional-at-point evaluation characterization is well sorted.          *)
Proposition FunctionalAtEvalCharac :
  CheckP (EvalOfClass.env) EvalOfClass.FunctionalAtEvalCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.FunctionalAtEvalCharac. checkP.
Qed.

(* The functional-at-point satisfaction theorem is well sorted.                 *)
Proposition FunctionalAtSatisfies :
  CheckP (EvalOfClass.env) EvalOfClass.FunctionalAtSatisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.FunctionalAtSatisfies. checkP.
Qed.

(* Evaluation without a value is empty is well sorted.                          *)
Proposition WhenNotHasValueAt :
  CheckP (EvalOfClass.env) EvalOfClass.WhenNotHasValueAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.WhenNotHasValueAt. checkP.
Qed.

(* Evaluation at a non-functional point is empty is well sorted.                *)
Proposition WhenNotFunctionalAt :
  CheckP (EvalOfClass.env) EvalOfClass.WhenNotFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.WhenNotFunctionalAt. checkP.
Qed.

(* Evaluation outside the domain is empty is well sorted.                       *)
Proposition WhenNotInDomain :
  CheckP (EvalOfClass.env) EvalOfClass.WhenNotInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.WhenNotInDomain. checkP.
Qed.

(* The functional evaluation characterization is well sorted.                   *)
Proposition Charac : CheckP (EvalOfClass.env) EvalOfClass.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.Charac. checkP.
Qed.

(* The functional satisfaction theorem is well sorted.                          *)
Proposition Satisfies : CheckP (EvalOfClass.env) EvalOfClass.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.Satisfies. checkP.
Qed.

(* The range membership theorem for functional evaluation is well sorted.       *)
Proposition IsInRange : CheckP (EvalOfClass.env) EvalOfClass.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.IsInRange. checkP.
Qed.

(* The image characterization by functional evaluation is well sorted.          *)
Proposition ImageCharac : CheckP (EvalOfClass.env) EvalOfClass.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold EvalOfClass.ImageCharac. checkP.
Qed.
