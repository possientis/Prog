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

Require Import ZF.Meta.Decl.Class.Relation.Fun.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for functions between classes is well sorted.           *)
Proposition Fun : CheckT (Fun.env) Fun.Fun.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Fun. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for Fun is well sorted.                            *)
Proposition EquivCompat : CheckP (Fun.env) Fun.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.EquivCompat. checkP.
Qed.

(* Left equivalence compatibility for Fun is well sorted.                       *)
Proposition EquivCompatL : CheckP (Fun.env) Fun.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.EquivCompatL. checkP.
Qed.

(* Middle equivalence compatibility for Fun is well sorted.                     *)
Proposition EquivCompatM : CheckP (Fun.env) Fun.EquivCompatM.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.EquivCompatM. checkP.
Qed.

(* Right equivalence compatibility for Fun is well sorted.                      *)
Proposition EquivCompatR : CheckP (Fun.env) Fun.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.EquivCompatR. checkP.
Qed.

(* The one-to-one criterion for Fun is well sorted.                             *)
Proposition IsOneToOne : CheckP (Fun.env) Fun.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.IsOneToOne. checkP.
Qed.

(* Fun equality characterization is well sorted.                                *)
Proposition Equal' : CheckP (Fun.env) Fun.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Equal'. checkP.
Qed.

(* Fun equality from pointwise equality is well sorted.                         *)
Proposition Equal : CheckP (Fun.env) Fun.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Equal. checkP.
Qed.

(* Image of the defining domain as range is well sorted.                        *)
Proposition ImageOfDomain : CheckP (Fun.env) Fun.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.ImageOfDomain. checkP.
Qed.

(* Smallness of images under Fun is well sorted.                                *)
Proposition ImageIsSmall : CheckP (Fun.env) Fun.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.ImageIsSmall. checkP.
Qed.

(* Smallness of functions from small defining domains is well sorted.           *)
Proposition IsSmall : CheckP (Fun.env) Fun.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.IsSmall. checkP.
Qed.

(* Inverse image of the range as the defining domain is well sorted.            *)
Proposition InvImageOfRange : CheckP (Fun.env) Fun.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.InvImageOfRange. checkP.
Qed.

(* Smallness of ranges from small defining domains is well sorted.              *)
Proposition RangeIsSmall : CheckP (Fun.env) Fun.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.RangeIsSmall. checkP.
Qed.

(* Smallness of domains into small codomains is well sorted.                    *)
Proposition DomainIsSmall : CheckP (Fun.env) Fun.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.DomainIsSmall. checkP.
Qed.

(* Composition closure for Fun is well sorted.                                  *)
Proposition Compose : CheckP (Fun.env) Fun.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Compose. checkP.
Qed.

(* Evaluation characterization for Fun is well sorted.                          *)
Proposition Eval' : CheckP (Fun.env) Fun.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Eval'. checkP.
Qed.

(* Evaluation of Fun is well sorted.                                            *)
Proposition Eval : CheckP (Fun.env) Fun.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Eval. checkP.
Qed.

(* Satisfaction at evaluated values for Fun is well sorted.                     *)
Proposition Satisfies : CheckP (Fun.env) Fun.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Satisfies. checkP.
Qed.

(* Codomain membership of evaluated values is well sorted.                      *)
Proposition IsInRange : CheckP (Fun.env) Fun.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.IsInRange. checkP.
Qed.

(* Class-image characterization by Fun evaluation is well sorted.               *)
Proposition ImageCharac : CheckP (Fun.env) Fun.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.ImageCharac. checkP.
Qed.

(* Set-image characterization by Fun evaluation is well sorted.                 *)
Proposition ImageSetCharac : CheckP (Fun.env) Fun.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization for Fun is well sorted.                    *)
Proposition DomainOfCompose : CheckP (Fun.env) Fun.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for Fun is well sorted.                                 *)
Proposition ComposeEval : CheckP (Fun.env) Fun.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.ComposeEval. checkP.
Qed.

(* Range characterization by Fun evaluation is well sorted.                     *)
Proposition RangeCharac : CheckP (Fun.env) Fun.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.RangeCharac. checkP.
Qed.

(* Nonempty range from nonempty defining domain is well sorted.                 *)
Proposition RangeIsNotEmpty : CheckP (Fun.env) Fun.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.RangeIsNotEmpty. checkP.
Qed.

(* Restriction-to-domain equality for Fun is well sorted.                       *)
Proposition IsRestrict : CheckP (Fun.env) Fun.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.IsRestrict. checkP.
Qed.

(* Restriction closure for Fun is well sorted.                                  *)
Proposition Restrict : CheckP (Fun.env) Fun.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (Fun.env) Fun.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fun.RestrictEqual. checkP.
Qed.

