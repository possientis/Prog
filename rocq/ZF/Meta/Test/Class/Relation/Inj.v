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

Require Import ZF.Meta.Decl.Class.Relation.Inj.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for injections between classes is well sorted.          *)
Proposition Inj : CheckT (Inj.env) Inj.Inj.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Inj. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for Inj is well sorted.                            *)
Proposition EquivCompat : CheckP (Inj.env) Inj.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EquivCompat. checkP.
Qed.

(* Left equivalence compatibility for Inj is well sorted.                       *)
Proposition EquivCompatL : CheckP (Inj.env) Inj.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EquivCompatL. checkP.
Qed.

(* Middle equivalence compatibility for Inj is well sorted.                     *)
Proposition EquivCompatM : CheckP (Inj.env) Inj.EquivCompatM.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EquivCompatM. checkP.
Qed.

(* Right equivalence compatibility for Inj is well sorted.                      *)
Proposition EquivCompatR : CheckP (Inj.env) Inj.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EquivCompatR. checkP.
Qed.

(* The function property of injections is well sorted.                          *)
Proposition IsFun : CheckP (Inj.env) Inj.IsFun.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.IsFun. checkP.
Qed.

(* Inj equality characterization is well sorted.                                *)
Proposition Equal' : CheckP (Inj.env) Inj.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Equal'. checkP.
Qed.

(* Inj equality from pointwise equality is well sorted.                         *)
Proposition Equal : CheckP (Inj.env) Inj.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Equal. checkP.
Qed.

(* Image of the defining domain as range is well sorted.                        *)
Proposition ImageOfDomain : CheckP (Inj.env) Inj.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ImageOfDomain. checkP.
Qed.

(* Smallness of images under Inj is well sorted.                                *)
Proposition ImageIsSmall : CheckP (Inj.env) Inj.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ImageIsSmall. checkP.
Qed.

(* Smallness of injections from small defining domains is well sorted.          *)
Proposition IsSmall : CheckP (Inj.env) Inj.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.IsSmall. checkP.
Qed.

(* Inverse image of the range as the defining domain is well sorted.            *)
Proposition InvImageOfRange : CheckP (Inj.env) Inj.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.InvImageOfRange. checkP.
Qed.

(* Smallness of ranges from small defining domains is well sorted.              *)
Proposition RangeIsSmall : CheckP (Inj.env) Inj.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.RangeIsSmall. checkP.
Qed.

(* Smallness of domains into small codomains is well sorted.                    *)
Proposition DomainIsSmall : CheckP (Inj.env) Inj.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.DomainIsSmall. checkP.
Qed.

(* Composition closure for Inj is well sorted.                                  *)
Proposition Compose : CheckP (Inj.env) Inj.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Compose. checkP.
Qed.

(* Evaluation characterization for Inj is well sorted.                          *)
Proposition Eval' : CheckP (Inj.env) Inj.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Eval'. checkP.
Qed.

(* Evaluation of Inj is well sorted.                                            *)
Proposition Eval : CheckP (Inj.env) Inj.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Eval. checkP.
Qed.

(* Satisfaction at evaluated values for Inj is well sorted.                     *)
Proposition Satisfies : CheckP (Inj.env) Inj.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Satisfies. checkP.
Qed.

(* Codomain membership of evaluated values is well sorted.                      *)
Proposition IsInRange : CheckP (Inj.env) Inj.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.IsInRange. checkP.
Qed.

(* Class-image characterization by Inj evaluation is well sorted.               *)
Proposition ImageCharac : CheckP (Inj.env) Inj.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ImageCharac. checkP.
Qed.

(* Set-image characterization by Inj evaluation is well sorted.                 *)
Proposition ImageSetCharac : CheckP (Inj.env) Inj.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization for Inj is well sorted.                    *)
Proposition DomainOfCompose : CheckP (Inj.env) Inj.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for Inj is well sorted.                                 *)
Proposition ComposeEval : CheckP (Inj.env) Inj.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ComposeEval. checkP.
Qed.

(* Range characterization by Inj evaluation is well sorted.                     *)
Proposition RangeCharac : CheckP (Inj.env) Inj.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.RangeCharac. checkP.
Qed.

(* Nonempty range from nonempty defining domain is well sorted.                 *)
Proposition RangeIsNotEmpty : CheckP (Inj.env) Inj.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.RangeIsNotEmpty. checkP.
Qed.

(* Restriction-to-domain equality for Inj is well sorted.                       *)
Proposition IsRestrict : CheckP (Inj.env) Inj.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.IsRestrict. checkP.
Qed.

(* Restriction closure for Inj is well sorted.                                  *)
Proposition Restrict : CheckP (Inj.env) Inj.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (Inj.env) Inj.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.RestrictEqual. checkP.
Qed.

(* Smallness of inverse images under Inj is well sorted.                        *)
Proposition InvImageIsSmall : CheckP (Inj.env) Inj.InvImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.InvImageIsSmall. checkP.
Qed.

(* Converse closure for Inj is well sorted.                                     *)
Proposition Converse : CheckP (Inj.env) Inj.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Converse. checkP.
Qed.

(* Domain membership of converse evaluation is well sorted.                     *)
Proposition ConverseEvalIsInDomain : CheckP (Inj.env) Inj.ConverseEvalIsInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ConverseEvalIsInDomain. checkP.
Qed.

(* Converse evaluation after evaluation is well sorted.                         *)
Proposition ConverseEvalOfEval : CheckP (Inj.env) Inj.ConverseEvalOfEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ConverseEvalOfEval. checkP.
Qed.

(* Evaluation after converse evaluation is well sorted.                         *)
Proposition EvalOfConverseEval : CheckP (Inj.env) Inj.EvalOfConverseEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EvalOfConverseEval. checkP.
Qed.

(* Inverse image of image equivalence is well sorted.                           *)
Proposition InvImageOfImage : CheckP (Inj.env) Inj.InvImageOfImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.InvImageOfImage. checkP.
Qed.

(* Image of inverse image equivalence is well sorted.                           *)
Proposition ImageOfInvImage : CheckP (Inj.env) Inj.ImageOfInvImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.ImageOfInvImage. checkP.
Qed.

(* Injectivity of Inj evaluation is well sorted.                                *)
Proposition EvalInjective : CheckP (Inj.env) Inj.EvalInjective.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EvalInjective. checkP.
Qed.

(* Evaluation membership in image is well sorted.                               *)
Proposition EvalInImage : CheckP (Inj.env) Inj.EvalInImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.EvalInImage. checkP.
Qed.

(* Preservation of binary intersections by image is well sorted.                *)
Proposition Inter2Image : CheckP (Inj.env) Inj.Inter2Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.Inter2Image. checkP.
Qed.

(* Preservation of class differences by image is well sorted.                   *)
Proposition DiffImage : CheckP (Inj.env) Inj.DiffImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inj.DiffImage. checkP.
Qed.

