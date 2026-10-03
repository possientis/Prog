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

Require Import ZF.Meta.Decl.Class.Relation.Bijection.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for bijection classes is well sorted.                   *)
Proposition Bijection : CheckT (Bijection.env) Bijection.Bijection.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Bijection. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for bijections is well sorted.                     *)
Proposition EquivCompat : CheckP (Bijection.env) Bijection.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.EquivCompat. checkP.
Qed.

(* The function property of bijections is well sorted.                          *)
Proposition IsFunction : CheckP (Bijection.env) Bijection.IsFunction.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.IsFunction. checkP.
Qed.

(* Bijection equality characterization is well sorted.                          *)
Proposition Equal' : CheckP (Bijection.env) Bijection.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Equal'. checkP.
Qed.

(* Bijection equality from domain and pointwise equality is well sorted.        *)
Proposition Equal : CheckP (Bijection.env) Bijection.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Equal. checkP.
Qed.

(* The image of the domain being the range is well sorted.                      *)
Proposition ImageOfDomain : CheckP (Bijection.env) Bijection.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ImageOfDomain. checkP.
Qed.

(* Smallness of images under bijections is well sorted.                         *)
Proposition ImageIsSmall : CheckP (Bijection.env) Bijection.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ImageIsSmall. checkP.
Qed.

(* Smallness of bijections from small domains is well sorted.                   *)
Proposition IsSmall : CheckP (Bijection.env) Bijection.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.IsSmall. checkP.
Qed.

(* The inverse image of the range being the domain is well sorted.              *)
Proposition InvImageOfRange : CheckP (Bijection.env) Bijection.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.InvImageOfRange. checkP.
Qed.

(* Smallness of ranges from small domains is well sorted.                       *)
Proposition RangeIsSmall : CheckP (Bijection.env) Bijection.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.RangeIsSmall. checkP.
Qed.

(* Smallness of domains from small ranges is well sorted.                       *)
Proposition DomainIsSmall : CheckP (Bijection.env) Bijection.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.DomainIsSmall. checkP.
Qed.

(* One-to-one composition closure as bijection is well sorted.                  *)
Proposition OneToOneCompose : CheckP (Bijection.env) Bijection.OneToOneCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.OneToOneCompose. checkP.
Qed.

(* Bijection composition closure is well sorted.                                *)
Proposition Compose : CheckP (Bijection.env) Bijection.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Compose. checkP.
Qed.

(* Evaluation characterization for bijections is well sorted.                   *)
Proposition Eval' : CheckP (Bijection.env) Bijection.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Eval'. checkP.
Qed.

(* Evaluation of bijections is well sorted.                                     *)
Proposition Eval : CheckP (Bijection.env) Bijection.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Eval. checkP.
Qed.

(* Satisfaction at evaluated values is well sorted.                             *)
Proposition Satisfies : CheckP (Bijection.env) Bijection.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Satisfies. checkP.
Qed.

(* Range membership of evaluated values is well sorted.                         *)
Proposition IsInRange : CheckP (Bijection.env) Bijection.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.IsInRange. checkP.
Qed.

(* Class-image characterization by evaluation is well sorted.                   *)
Proposition ImageCharac : CheckP (Bijection.env) Bijection.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ImageCharac. checkP.
Qed.

(* Set-image characterization by evaluation is well sorted.                     *)
Proposition ImageSetCharac : CheckP (Bijection.env) Bijection.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization is well sorted.                            *)
Proposition DomainOfCompose : CheckP (Bijection.env) Bijection.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for bijections is well sorted.                          *)
Proposition ComposeEval : CheckP (Bijection.env) Bijection.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ComposeEval. checkP.
Qed.

(* Range characterization by evaluation is well sorted.                         *)
Proposition RangeCharac : CheckP (Bijection.env) Bijection.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.RangeCharac. checkP.
Qed.

(* Nonempty range from nonempty domain is well sorted.                          *)
Proposition RangeIsNotEmpty : CheckP (Bijection.env) Bijection.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.RangeIsNotEmpty. checkP.
Qed.

(* Bijection equality with restriction to the domain is well sorted.            *)
Proposition IsRestrict : CheckP (Bijection.env) Bijection.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.IsRestrict. checkP.
Qed.

(* Restriction closure for bijections is well sorted.                           *)
Proposition Restrict : CheckP (Bijection.env) Bijection.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (Bijection.env) Bijection.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.RestrictEqual. checkP.
Qed.

(* Smallness of inverse images under bijections is well sorted.                 *)
Proposition InvImageIsSmall : CheckP (Bijection.env) Bijection.InvImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.InvImageIsSmall. checkP.
Qed.

(* The converse function property is well sorted.                               *)
Proposition ConverseIsFunction : CheckP (Bijection.env) Bijection.ConverseIsFunction.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ConverseIsFunction. checkP.
Qed.

(* Converse closure for bijections is well sorted.                              *)
Proposition Converse : CheckP (Bijection.env) Bijection.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Converse. checkP.
Qed.

(* Domain membership of converse evaluation is well sorted.                     *)
Proposition ConverseEvalIsInDomain : CheckP (Bijection.env) Bijection.ConverseEvalIsInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ConverseEvalIsInDomain. checkP.
Qed.

(* Converse evaluation after evaluation is well sorted.                         *)
Proposition ConverseEvalOfEval : CheckP (Bijection.env) Bijection.ConverseEvalOfEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ConverseEvalOfEval. checkP.
Qed.

(* Evaluation after converse evaluation is well sorted.                         *)
Proposition EvalOfConverseEval : CheckP (Bijection.env) Bijection.EvalOfConverseEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.EvalOfConverseEval. checkP.
Qed.

(* Inverse image of image equivalence is well sorted.                           *)
Proposition InvImageOfImage : CheckP (Bijection.env) Bijection.InvImageOfImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.InvImageOfImage. checkP.
Qed.

(* Image of inverse image equivalence is well sorted.                           *)
Proposition ImageOfInvImage : CheckP (Bijection.env) Bijection.ImageOfInvImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.ImageOfInvImage. checkP.
Qed.

(* Injectivity of evaluation is well sorted.                                    *)
Proposition EvalInjective : CheckP (Bijection.env) Bijection.EvalInjective.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.EvalInjective. checkP.
Qed.

(* Evaluation membership in image is well sorted.                               *)
Proposition EvalInImage : CheckP (Bijection.env) Bijection.EvalInImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.EvalInImage. checkP.
Qed.

(* Preservation of binary intersections by image is well sorted.                *)
Proposition Inter2Image : CheckP (Bijection.env) Bijection.Inter2Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.Inter2Image. checkP.
Qed.

(* Preservation of class differences by image is well sorted.                   *)
Proposition DiffImage : CheckP (Bijection.env) Bijection.DiffImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bijection.DiffImage. checkP.
Qed.

