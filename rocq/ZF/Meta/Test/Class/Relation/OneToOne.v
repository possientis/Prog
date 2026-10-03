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

Require Import ZF.Meta.Decl.Class.Relation.OneToOne.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for one-to-one classes is well sorted.                  *)
Proposition OneToOne : CheckT (OneToOne.env) OneToOne.OneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.OneToOne. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for one-to-one classes is well sorted.             *)
Proposition EquivCompat : CheckP (OneToOne.env) OneToOne.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.EquivCompat. checkP.
Qed.

(* Left-coordinate uniqueness for one-to-one classes is well sorted.            *)
Proposition CharacL : CheckP (OneToOne.env) OneToOne.CharacL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.CharacL. checkP.
Qed.

(* Right-coordinate uniqueness for one-to-one classes is well sorted.           *)
Proposition CharacR : CheckP (OneToOne.env) OneToOne.CharacR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.CharacR. checkP.
Qed.

(* Smallness of images under one-to-one classes is well sorted.                 *)
Proposition ImageIsSmall : CheckP (OneToOne.env) OneToOne.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.ImageIsSmall. checkP.
Qed.

(* Smallness of inverse images under one-to-one classes is well sorted.         *)
Proposition InvImageIsSmall : CheckP (OneToOne.env) OneToOne.InvImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.InvImageIsSmall. checkP.
Qed.

(* Coordinate equivalence for one-to-one classes is well sorted.                *)
Proposition CoordEquiv : CheckP (OneToOne.env) OneToOne.CoordEquiv.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.CoordEquiv. checkP.
Qed.

(* One-to-one converse closure is well sorted.                                  *)
Proposition Converse : CheckP (OneToOne.env) OneToOne.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.Converse. checkP.
Qed.

(* Evaluation characterization for one-to-one classes is well sorted.           *)
Proposition Eval' : CheckP (OneToOne.env) OneToOne.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.Eval'. checkP.
Qed.

(* Evaluation of one-to-one classes is well sorted.                             *)
Proposition Eval : CheckP (OneToOne.env) OneToOne.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.Eval. checkP.
Qed.

(* Satisfaction at evaluated values is well sorted.                             *)
Proposition Satisfies : CheckP (OneToOne.env) OneToOne.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.Satisfies. checkP.
Qed.

(* Range membership of evaluated values is well sorted.                         *)
Proposition IsInRange : CheckP (OneToOne.env) OneToOne.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.IsInRange. checkP.
Qed.

(* Image characterization by evaluation is well sorted.                         *)
Proposition ImageCharac : CheckP (OneToOne.env) OneToOne.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.ImageCharac. checkP.
Qed.

(* Domain membership of converse evaluation is well sorted.                     *)
Proposition ConverseEvalIsInDomain : CheckP (OneToOne.env) OneToOne.ConverseEvalIsInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.ConverseEvalIsInDomain. checkP.
Qed.

(* Composition closure for one-to-one classes is well sorted.                   *)
Proposition Compose : CheckP (OneToOne.env) OneToOne.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.Compose. checkP.
Qed.

(* Converse evaluation after evaluation is well sorted.                         *)
Proposition ConverseEvalOfEval : CheckP (OneToOne.env) OneToOne.ConverseEvalOfEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.ConverseEvalOfEval. checkP.
Qed.

(* Evaluation after converse evaluation is well sorted.                         *)
Proposition EvalOfConverseEval : CheckP (OneToOne.env) OneToOne.EvalOfConverseEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.EvalOfConverseEval. checkP.
Qed.

(* Composite domain characterization is well sorted.                            *)
Proposition DomainOfCompose : CheckP (OneToOne.env) OneToOne.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for one-to-one classes is well sorted.                  *)
Proposition ComposeEval : CheckP (OneToOne.env) OneToOne.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.ComposeEval. checkP.
Qed.

(* Inverse image of image equivalence is well sorted.                           *)
Proposition InvImageOfImage : CheckP (OneToOne.env) OneToOne.InvImageOfImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.InvImageOfImage. checkP.
Qed.

(* Image of inverse image equivalence is well sorted.                           *)
Proposition ImageOfInvImage : CheckP (OneToOne.env) OneToOne.ImageOfInvImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.ImageOfInvImage. checkP.
Qed.

(* Injectivity of evaluation is well sorted.                                    *)
Proposition EvalInjective : CheckP (OneToOne.env) OneToOne.EvalInjective.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.EvalInjective. checkP.
Qed.

(* Functional injectivity criterion is well sorted.                             *)
Proposition WhenFunctional : CheckP (OneToOne.env) OneToOne.WhenFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.WhenFunctional. checkP.
Qed.

(* Evaluation membership in image is well sorted.                               *)
Proposition EvalInImage : CheckP (OneToOne.env) OneToOne.EvalInImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.EvalInImage. checkP.
Qed.

(* Restriction closure for one-to-one classes is well sorted.                   *)
Proposition Restrict : CheckP (OneToOne.env) OneToOne.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold OneToOne.Restrict. checkP.
Qed.
