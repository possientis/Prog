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

Require Import ZF.Meta.Decl.Class.Relation.Onto.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for surjections between classes is well sorted.         *)
Proposition Onto : CheckT (Onto.env) Onto.Onto.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Onto. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for Onto is well sorted.                           *)
Proposition EquivCompat : CheckP (Onto.env) Onto.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.EquivCompat. checkP.
Qed.

(* Left equivalence compatibility for Onto is well sorted.                      *)
Proposition EquivCompatL : CheckP (Onto.env) Onto.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.EquivCompatL. checkP.
Qed.

(* Middle equivalence compatibility for Onto is well sorted.                    *)
Proposition EquivCompatM : CheckP (Onto.env) Onto.EquivCompatM.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.EquivCompatM. checkP.
Qed.

(* Right equivalence compatibility for Onto is well sorted.                     *)
Proposition EquivCompatR : CheckP (Onto.env) Onto.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.EquivCompatR. checkP.
Qed.

(* The function property of surjections is well sorted.                         *)
Proposition IsFun : CheckP (Onto.env) Onto.IsFun.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.IsFun. checkP.
Qed.

(* The one-to-one criterion for Onto is well sorted.                            *)
Proposition IsOneToOne : CheckP (Onto.env) Onto.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.IsOneToOne. checkP.
Qed.

(* Onto equality characterization is well sorted.                               *)
Proposition Equal' : CheckP (Onto.env) Onto.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Equal'. checkP.
Qed.

(* Onto equality from pointwise equality is well sorted.                        *)
Proposition Equal : CheckP (Onto.env) Onto.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Equal. checkP.
Qed.

(* Image of the defining domain as codomain is well sorted.                     *)
Proposition ImageOfDomain : CheckP (Onto.env) Onto.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.ImageOfDomain. checkP.
Qed.

(* Smallness of images under Onto is well sorted.                               *)
Proposition ImageIsSmall : CheckP (Onto.env) Onto.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.ImageIsSmall. checkP.
Qed.

(* Smallness of surjections from small defining domains is well sorted.         *)
Proposition IsSmall : CheckP (Onto.env) Onto.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.IsSmall. checkP.
Qed.

(* Inverse image of the codomain as the domain is well sorted.                  *)
Proposition InvImageOfRange : CheckP (Onto.env) Onto.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.InvImageOfRange. checkP.
Qed.

(* Smallness of codomains from small defining domains is well sorted.           *)
Proposition RangeIsSmall : CheckP (Onto.env) Onto.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.RangeIsSmall. checkP.
Qed.

(* Smallness of domains into small codomains is well sorted.                    *)
Proposition DomainIsSmall : CheckP (Onto.env) Onto.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.DomainIsSmall. checkP.
Qed.

(* Composition closure for Onto is well sorted.                                 *)
Proposition Compose : CheckP (Onto.env) Onto.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Compose. checkP.
Qed.

(* Evaluation characterization for Onto is well sorted.                         *)
Proposition Eval' : CheckP (Onto.env) Onto.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Eval'. checkP.
Qed.

(* Evaluation of Onto is well sorted.                                           *)
Proposition Eval : CheckP (Onto.env) Onto.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Eval. checkP.
Qed.

(* Satisfaction at evaluated values for Onto is well sorted.                    *)
Proposition Satisfies : CheckP (Onto.env) Onto.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Satisfies. checkP.
Qed.

(* Codomain membership of evaluated values is well sorted.                      *)
Proposition IsInRange : CheckP (Onto.env) Onto.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.IsInRange. checkP.
Qed.

(* Class-image characterization by Onto evaluation is well sorted.              *)
Proposition ImageCharac : CheckP (Onto.env) Onto.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.ImageCharac. checkP.
Qed.

(* Set-image characterization by Onto evaluation is well sorted.                *)
Proposition ImageSetCharac : CheckP (Onto.env) Onto.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization for Onto is well sorted.                   *)
Proposition DomainOfCompose : CheckP (Onto.env) Onto.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for Onto is well sorted.                                *)
Proposition ComposeEval : CheckP (Onto.env) Onto.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.ComposeEval. checkP.
Qed.

(* Codomain characterization by Onto evaluation is well sorted.                 *)
Proposition RangeCharac : CheckP (Onto.env) Onto.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.RangeCharac. checkP.
Qed.

(* Nonempty codomain from nonempty defining domain is well sorted.              *)
Proposition RangeIsNotEmpty : CheckP (Onto.env) Onto.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.RangeIsNotEmpty. checkP.
Qed.

(* Restriction-to-domain equality for Onto is well sorted.                      *)
Proposition IsRestrict : CheckP (Onto.env) Onto.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.IsRestrict. checkP.
Qed.

(* Restriction closure for Onto is well sorted.                                 *)
Proposition Restrict : CheckP (Onto.env) Onto.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (Onto.env) Onto.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Onto.RestrictEqual. checkP.
Qed.

