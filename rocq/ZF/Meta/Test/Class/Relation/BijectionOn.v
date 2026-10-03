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

Require Import ZF.Meta.Decl.Class.Relation.BijectionOn.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for bijections on classes is well sorted.               *)
Proposition BijectionOn : CheckT (BijectionOn.env) BijectionOn.BijectionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.BijectionOn. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for BijectionOn is well sorted.                    *)
Proposition EquivCompat : CheckP (BijectionOn.env) BijectionOn.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.EquivCompat. checkP.
Qed.

(* Left equivalence compatibility for BijectionOn is well sorted.               *)
Proposition EquivCompatL : CheckP (BijectionOn.env) BijectionOn.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.EquivCompatL. checkP.
Qed.

(* Right equivalence compatibility for BijectionOn is well sorted.              *)
Proposition EquivCompatR : CheckP (BijectionOn.env) BijectionOn.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.EquivCompatR. checkP.
Qed.

(* The function-on property of BijectionOn is well sorted.                      *)
Proposition IsFunctionOn : CheckP (BijectionOn.env) BijectionOn.IsFunctionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.IsFunctionOn. checkP.
Qed.

(* BijectionOn equality characterization is well sorted.                        *)
Proposition Equal' : CheckP (BijectionOn.env) BijectionOn.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Equal'. checkP.
Qed.

(* BijectionOn equality from pointwise equality is well sorted.                 *)
Proposition Equal : CheckP (BijectionOn.env) BijectionOn.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Equal. checkP.
Qed.

(* Image of the defining domain as range is well sorted.                        *)
Proposition ImageOfDomain : CheckP (BijectionOn.env) BijectionOn.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ImageOfDomain. checkP.
Qed.

(* Smallness of images under BijectionOn is well sorted.                        *)
Proposition ImageIsSmall : CheckP (BijectionOn.env) BijectionOn.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ImageIsSmall. checkP.
Qed.

(* Smallness of bijections from small defining domains is well sorted.          *)
Proposition IsSmall : CheckP (BijectionOn.env) BijectionOn.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.IsSmall. checkP.
Qed.

(* Inverse image of the range as the defining domain is well sorted.            *)
Proposition InvImageOfRange : CheckP (BijectionOn.env) BijectionOn.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.InvImageOfRange. checkP.
Qed.

(* Smallness of ranges from small defining domains is well sorted.              *)
Proposition RangeIsSmall : CheckP (BijectionOn.env) BijectionOn.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.RangeIsSmall. checkP.
Qed.

(* Smallness of domains from small ranges is well sorted.                       *)
Proposition DomainIsSmall : CheckP (BijectionOn.env) BijectionOn.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.DomainIsSmall. checkP.
Qed.

(* Composition closure for BijectionOn is well sorted.                          *)
Proposition Compose : CheckP (BijectionOn.env) BijectionOn.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Compose. checkP.
Qed.

(* Evaluation characterization for BijectionOn is well sorted.                  *)
Proposition Eval' : CheckP (BijectionOn.env) BijectionOn.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Eval'. checkP.
Qed.

(* Evaluation of BijectionOn is well sorted.                                    *)
Proposition Eval : CheckP (BijectionOn.env) BijectionOn.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Eval. checkP.
Qed.

(* Satisfaction at evaluated values for BijectionOn is well sorted.             *)
Proposition Satisfies : CheckP (BijectionOn.env) BijectionOn.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Satisfies. checkP.
Qed.

(* Range membership of evaluated values is well sorted.                         *)
Proposition IsInRange : CheckP (BijectionOn.env) BijectionOn.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.IsInRange. checkP.
Qed.

(* Class-image characterization by BijectionOn evaluation is well sorted.       *)
Proposition ImageCharac : CheckP (BijectionOn.env) BijectionOn.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ImageCharac. checkP.
Qed.

(* Set-image characterization by BijectionOn evaluation is well sorted.         *)
Proposition ImageSetCharac : CheckP (BijectionOn.env) BijectionOn.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization for BijectionOn is well sorted.            *)
Proposition DomainOfCompose : CheckP (BijectionOn.env) BijectionOn.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for BijectionOn is well sorted.                         *)
Proposition ComposeEval : CheckP (BijectionOn.env) BijectionOn.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ComposeEval. checkP.
Qed.

(* Range characterization by BijectionOn evaluation is well sorted.             *)
Proposition RangeCharac : CheckP (BijectionOn.env) BijectionOn.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.RangeCharac. checkP.
Qed.

(* Nonempty range from nonempty defining domain is well sorted.                 *)
Proposition RangeIsNotEmpty : CheckP (BijectionOn.env) BijectionOn.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.RangeIsNotEmpty. checkP.
Qed.

(* Restriction-to-domain equality for BijectionOn is well sorted.               *)
Proposition IsRestrict : CheckP (BijectionOn.env) BijectionOn.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.IsRestrict. checkP.
Qed.

(* Restriction closure for BijectionOn is well sorted.                          *)
Proposition Restrict : CheckP (BijectionOn.env) BijectionOn.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (BijectionOn.env) BijectionOn.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.RestrictEqual. checkP.
Qed.

(* Smallness of inverse images under BijectionOn is well sorted.                *)
Proposition InvImageIsSmall : CheckP (BijectionOn.env) BijectionOn.InvImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.InvImageIsSmall. checkP.
Qed.

(* Converse closure for BijectionOn is well sorted.                             *)
Proposition Converse : CheckP (BijectionOn.env) BijectionOn.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Converse. checkP.
Qed.

(* Domain membership of converse evaluation is well sorted.                     *)
Proposition ConverseEvalIsInDomain : CheckP (BijectionOn.env) BijectionOn.ConverseEvalIsInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ConverseEvalIsInDomain. checkP.
Qed.

(* Converse evaluation after evaluation is well sorted.                         *)
Proposition ConverseEvalOfEval : CheckP (BijectionOn.env) BijectionOn.ConverseEvalOfEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ConverseEvalOfEval. checkP.
Qed.

(* Evaluation after converse evaluation is well sorted.                         *)
Proposition EvalOfConverseEval : CheckP (BijectionOn.env) BijectionOn.EvalOfConverseEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.EvalOfConverseEval. checkP.
Qed.

(* Inverse image of image equivalence is well sorted.                           *)
Proposition InvImageOfImage : CheckP (BijectionOn.env) BijectionOn.InvImageOfImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.InvImageOfImage. checkP.
Qed.

(* Image of inverse image equivalence is well sorted.                           *)
Proposition ImageOfInvImage : CheckP (BijectionOn.env) BijectionOn.ImageOfInvImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.ImageOfInvImage. checkP.
Qed.

(* Injectivity of BijectionOn evaluation is well sorted.                        *)
Proposition EvalInjective : CheckP (BijectionOn.env) BijectionOn.EvalInjective.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.EvalInjective. checkP.
Qed.

(* Evaluation membership in image is well sorted.                               *)
Proposition EvalInImage : CheckP (BijectionOn.env) BijectionOn.EvalInImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.EvalInImage. checkP.
Qed.

(* Every bijection being a bijection on its domain is well sorted.              *)
Proposition BijectionIsBijectionOn : CheckP (BijectionOn.env) BijectionOn.BijectionIsBijectionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.BijectionIsBijectionOn. checkP.
Qed.

(* Preservation of binary intersections by image is well sorted.                *)
Proposition Inter2Image : CheckP (BijectionOn.env) BijectionOn.Inter2Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.Inter2Image. checkP.
Qed.

(* Preservation of class differences by image is well sorted.                   *)
Proposition DiffImage : CheckP (BijectionOn.env) BijectionOn.DiffImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold BijectionOn.DiffImage. checkP.
Qed.

