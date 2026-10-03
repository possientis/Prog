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

Require Import ZF.Meta.Decl.Class.Relation.FunctionOn.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for functions on classes is well sorted.                *)
Proposition FunctionOn : CheckT (FunctionOn.env) FunctionOn.FunctionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.FunctionOn. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for FunctionOn is well sorted.                     *)
Proposition EquivCompat : CheckP (FunctionOn.env) FunctionOn.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.EquivCompat. checkP.
Qed.

(* Left equivalence compatibility for FunctionOn is well sorted.                *)
Proposition EquivCompatL : CheckP (FunctionOn.env) FunctionOn.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.EquivCompatL. checkP.
Qed.

(* Right equivalence compatibility for FunctionOn is well sorted.               *)
Proposition EquivCompatR : CheckP (FunctionOn.env) FunctionOn.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.EquivCompatR. checkP.
Qed.

(* The one-to-one criterion for FunctionOn is well sorted.                      *)
Proposition IsOneToOne : CheckP (FunctionOn.env) FunctionOn.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.IsOneToOne. checkP.
Qed.

(* FunctionOn equality characterization is well sorted.                         *)
Proposition Equal' : CheckP (FunctionOn.env) FunctionOn.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Equal'. checkP.
Qed.

(* FunctionOn equality from pointwise equality is well sorted.                  *)
Proposition Equal : CheckP (FunctionOn.env) FunctionOn.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Equal. checkP.
Qed.

(* Image of the defining domain as range is well sorted.                        *)
Proposition ImageOfDomain : CheckP (FunctionOn.env) FunctionOn.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.ImageOfDomain. checkP.
Qed.

(* Smallness of images under FunctionOn is well sorted.                         *)
Proposition ImageIsSmall : CheckP (FunctionOn.env) FunctionOn.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.ImageIsSmall. checkP.
Qed.

(* Smallness of functions from small defining domains is well sorted.           *)
Proposition IsSmall : CheckP (FunctionOn.env) FunctionOn.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.IsSmall. checkP.
Qed.

(* Inverse image of the range as the defining domain is well sorted.            *)
Proposition InvImageOfRange : CheckP (FunctionOn.env) FunctionOn.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.InvImageOfRange. checkP.
Qed.

(* Smallness of ranges from small defining domains is well sorted.              *)
Proposition RangeIsSmall : CheckP (FunctionOn.env) FunctionOn.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.RangeIsSmall. checkP.
Qed.

(* Smallness of domains from small ranges is well sorted.                       *)
Proposition DomainIsSmall : CheckP (FunctionOn.env) FunctionOn.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.DomainIsSmall. checkP.
Qed.

(* Composition closure for FunctionOn is well sorted.                           *)
Proposition Compose : CheckP (FunctionOn.env) FunctionOn.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Compose. checkP.
Qed.

(* Evaluation characterization for FunctionOn is well sorted.                   *)
Proposition Eval' : CheckP (FunctionOn.env) FunctionOn.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Eval'. checkP.
Qed.

(* Evaluation of FunctionOn is well sorted.                                     *)
Proposition Eval : CheckP (FunctionOn.env) FunctionOn.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Eval. checkP.
Qed.

(* Satisfaction at evaluated values for FunctionOn is well sorted.              *)
Proposition Satisfies : CheckP (FunctionOn.env) FunctionOn.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Satisfies. checkP.
Qed.

(* Range membership of evaluated values is well sorted.                         *)
Proposition IsInRange : CheckP (FunctionOn.env) FunctionOn.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.IsInRange. checkP.
Qed.

(* Class-image characterization by FunctionOn evaluation is well sorted.        *)
Proposition ImageCharac : CheckP (FunctionOn.env) FunctionOn.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.ImageCharac. checkP.
Qed.

(* Set-image characterization by FunctionOn evaluation is well sorted.          *)
Proposition ImageSetCharac : CheckP (FunctionOn.env) FunctionOn.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization for FunctionOn is well sorted.             *)
Proposition DomainOfCompose : CheckP (FunctionOn.env) FunctionOn.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for FunctionOn is well sorted.                          *)
Proposition ComposeEval : CheckP (FunctionOn.env) FunctionOn.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.ComposeEval. checkP.
Qed.

(* Range characterization by FunctionOn evaluation is well sorted.              *)
Proposition RangeCharac : CheckP (FunctionOn.env) FunctionOn.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.RangeCharac. checkP.
Qed.

(* Nonempty range from nonempty defining domain is well sorted.                 *)
Proposition RangeIsNotEmpty : CheckP (FunctionOn.env) FunctionOn.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.RangeIsNotEmpty. checkP.
Qed.

(* Restriction-to-domain equality for FunctionOn is well sorted.                *)
Proposition IsRestrict : CheckP (FunctionOn.env) FunctionOn.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.IsRestrict. checkP.
Qed.

(* Restriction closure for FunctionOn is well sorted.                           *)
Proposition Restrict : CheckP (FunctionOn.env) FunctionOn.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (FunctionOn.env) FunctionOn.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.RestrictEqual. checkP.
Qed.

(* Every function being a function on its domain is well sorted.                *)
Proposition FunctionIsFunctionOn : CheckP (FunctionOn.env) FunctionOn.FunctionIsFunctionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionOn.FunctionIsFunctionOn. checkP.
Qed.

