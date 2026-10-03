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

Require Import ZF.Meta.Decl.Class.Relation.Bij.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for bijections between classes is well sorted.          *)
Proposition Bij : CheckT (Bij.env) Bij.Bij.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Bij. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for Bij is well sorted.                            *)
Proposition EquivCompat : CheckP (Bij.env) Bij.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EquivCompat. checkP.
Qed.

(* Left equivalence compatibility for Bij is well sorted.                       *)
Proposition EquivCompatL : CheckP (Bij.env) Bij.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EquivCompatL. checkP.
Qed.

(* Middle equivalence compatibility for Bij is well sorted.                     *)
Proposition EquivCompatM : CheckP (Bij.env) Bij.EquivCompatM.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EquivCompatM. checkP.
Qed.

(* Right equivalence compatibility for Bij is well sorted.                      *)
Proposition EquivCompatR : CheckP (Bij.env) Bij.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EquivCompatR. checkP.
Qed.

(* The function property of bijections is well sorted.                          *)
Proposition IsFun : CheckP (Bij.env) Bij.IsFun.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsFun. checkP.
Qed.

(* The one-to-one property of bijections is well sorted.                        *)
Proposition IsOneToOne : CheckP (Bij.env) Bij.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsOneToOne. checkP.
Qed.

(* The defining-domain property of bijections is well sorted.                   *)
Proposition IsFunctionOn : CheckP (Bij.env) Bij.IsFunctionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsFunctionOn. checkP.
Qed.

(* The injection property of bijections is well sorted.                         *)
Proposition IsInj : CheckP (Bij.env) Bij.IsInj.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsInj. checkP.
Qed.

(* The surjection property of bijections is well sorted.                        *)
Proposition IsOnto : CheckP (Bij.env) Bij.IsOnto.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsOnto. checkP.
Qed.

(* Bij equality characterization is well sorted.                                *)
Proposition Equal' : CheckP (Bij.env) Bij.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Equal'. checkP.
Qed.

(* Bij equality from pointwise equality is well sorted.                         *)
Proposition Equal : CheckP (Bij.env) Bij.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Equal. checkP.
Qed.

(* Image of the defining domain as codomain is well sorted.                     *)
Proposition ImageOfDomain : CheckP (Bij.env) Bij.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ImageOfDomain. checkP.
Qed.

(* Smallness of images under Bij is well sorted.                                *)
Proposition ImageIsSmall : CheckP (Bij.env) Bij.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ImageIsSmall. checkP.
Qed.

(* Smallness of bijections from small defining domains is well sorted.          *)
Proposition IsSmall : CheckP (Bij.env) Bij.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsSmall. checkP.
Qed.

(* Inverse image of the codomain as the domain is well sorted.                  *)
Proposition InvImageOfRange : CheckP (Bij.env) Bij.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.InvImageOfRange. checkP.
Qed.

(* Smallness of codomains from small defining domains is well sorted.           *)
Proposition RangeIsSmall : CheckP (Bij.env) Bij.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.RangeIsSmall. checkP.
Qed.

(* Smallness of domains into small codomains is well sorted.                    *)
Proposition DomainIsSmall : CheckP (Bij.env) Bij.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.DomainIsSmall. checkP.
Qed.

(* Composition closure for Bij is well sorted.                                  *)
Proposition Compose : CheckP (Bij.env) Bij.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Compose. checkP.
Qed.

(* Evaluation characterization for Bij is well sorted.                          *)
Proposition Eval' : CheckP (Bij.env) Bij.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Eval'. checkP.
Qed.

(* Evaluation of Bij is well sorted.                                            *)
Proposition Eval : CheckP (Bij.env) Bij.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Eval. checkP.
Qed.

(* Satisfaction at evaluated values for Bij is well sorted.                     *)
Proposition Satisfies : CheckP (Bij.env) Bij.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Satisfies. checkP.
Qed.

(* Codomain membership of evaluated values is well sorted.                      *)
Proposition IsInRange : CheckP (Bij.env) Bij.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsInRange. checkP.
Qed.

(* Class-image characterization by Bij evaluation is well sorted.               *)
Proposition ImageCharac : CheckP (Bij.env) Bij.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ImageCharac. checkP.
Qed.

(* Set-image characterization by Bij evaluation is well sorted.                 *)
Proposition ImageSetCharac : CheckP (Bij.env) Bij.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization for Bij is well sorted.                    *)
Proposition DomainOfCompose : CheckP (Bij.env) Bij.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for Bij is well sorted.                                 *)
Proposition ComposeEval : CheckP (Bij.env) Bij.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ComposeEval. checkP.
Qed.

(* Codomain characterization by Bij evaluation is well sorted.                  *)
Proposition RangeCharac : CheckP (Bij.env) Bij.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.RangeCharac. checkP.
Qed.

(* Image inclusion into the codomain is well sorted.                            *)
Proposition ImageIncl : CheckP (Bij.env) Bij.ImageIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ImageIncl. checkP.
Qed.

(* Nonempty codomain from nonempty defining domain is well sorted.              *)
Proposition RangeIsNotEmpty : CheckP (Bij.env) Bij.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.RangeIsNotEmpty. checkP.
Qed.

(* Restriction-to-domain equality for Bij is well sorted.                       *)
Proposition IsRestrict : CheckP (Bij.env) Bij.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.IsRestrict. checkP.
Qed.

(* Restriction closure for Bij is well sorted.                                  *)
Proposition Restrict : CheckP (Bij.env) Bij.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (Bij.env) Bij.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.RestrictEqual. checkP.
Qed.

(* Smallness of inverse images under Bij is well sorted.                        *)
Proposition InvImageIsSmall : CheckP (Bij.env) Bij.InvImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.InvImageIsSmall. checkP.
Qed.

(* Converse closure for Bij is well sorted.                                     *)
Proposition Converse : CheckP (Bij.env) Bij.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Converse. checkP.
Qed.

(* Domain membership of converse evaluation is well sorted.                     *)
Proposition ConverseEvalIsInDomain : CheckP (Bij.env) Bij.ConverseEvalIsInDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ConverseEvalIsInDomain. checkP.
Qed.

(* Converse evaluation after evaluation is well sorted.                         *)
Proposition ConverseEvalOfEval : CheckP (Bij.env) Bij.ConverseEvalOfEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ConverseEvalOfEval. checkP.
Qed.

(* Evaluation after converse evaluation is well sorted.                         *)
Proposition EvalOfConverseEval : CheckP (Bij.env) Bij.EvalOfConverseEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EvalOfConverseEval. checkP.
Qed.

(* Inverse image of image equivalence is well sorted.                           *)
Proposition InvImageOfImage : CheckP (Bij.env) Bij.InvImageOfImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.InvImageOfImage. checkP.
Qed.

(* Image of inverse image equivalence is well sorted.                           *)
Proposition ImageOfInvImage : CheckP (Bij.env) Bij.ImageOfInvImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.ImageOfInvImage. checkP.
Qed.

(* Injectivity of Bij evaluation is well sorted.                                *)
Proposition EvalInjective : CheckP (Bij.env) Bij.EvalInjective.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EvalInjective. checkP.
Qed.

(* Evaluation membership in image is well sorted.                               *)
Proposition EvalInImage : CheckP (Bij.env) Bij.EvalInImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.EvalInImage. checkP.
Qed.

(* Preservation of binary intersections by image is well sorted.                *)
Proposition Inter2Image : CheckP (Bij.env) Bij.Inter2Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.Inter2Image. checkP.
Qed.

(* Preservation of class differences by image is well sorted.                   *)
Proposition DiffImage : CheckP (Bij.env) Bij.DiffImage.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bij.DiffImage. checkP.
Qed.

