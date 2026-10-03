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

Require Import ZF.Meta.Decl.Class.Relation.Function.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for function classes is well sorted.                    *)
Proposition Function : CheckT (Function.env) Function.Function.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Function. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for functions is well sorted.                      *)
Proposition EquivCompat : CheckP (Function.env) Function.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.EquivCompat. checkP.
Qed.

(* The one-to-one criterion for functions is well sorted.                       *)
Proposition IsOneToOne : CheckP (Function.env) Function.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.IsOneToOne. checkP.
Qed.

(* Function equality characterization is well sorted.                           *)
Proposition Equal' : CheckP (Function.env) Function.Equal'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Equal'. checkP.
Qed.

(* Function equality from domain and pointwise equality is well sorted.         *)
Proposition Equal : CheckP (Function.env) Function.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Equal. checkP.
Qed.

(* The image of the domain being the range is well sorted.                      *)
Proposition ImageOfDomain : CheckP (Function.env) Function.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.ImageOfDomain. checkP.
Qed.

(* Smallness of images under functions is well sorted.                          *)
Proposition ImageIsSmall : CheckP (Function.env) Function.ImageIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.ImageIsSmall. checkP.
Qed.

(* Smallness of functions from small domains is well sorted.                    *)
Proposition IsSmall : CheckP (Function.env) Function.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.IsSmall. checkP.
Qed.

(* The inverse image of the range being the domain is well sorted.              *)
Proposition InvImageOfRange : CheckP (Function.env) Function.InvImageOfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.InvImageOfRange. checkP.
Qed.

(* Smallness of ranges from small domains is well sorted.                       *)
Proposition RangeIsSmall : CheckP (Function.env) Function.RangeIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.RangeIsSmall. checkP.
Qed.

(* Smallness of domains from small ranges is well sorted.                       *)
Proposition DomainIsSmall : CheckP (Function.env) Function.DomainIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.DomainIsSmall. checkP.
Qed.

(* Functional composition closure is well sorted.                               *)
Proposition FunctionalCompose : CheckP (Function.env) Function.FunctionalCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.FunctionalCompose. checkP.
Qed.

(* Function composition closure is well sorted.                                 *)
Proposition Compose : CheckP (Function.env) Function.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Compose. checkP.
Qed.

(* Evaluation characterization for functions is well sorted.                    *)
Proposition Eval' : CheckP (Function.env) Function.Eval'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Eval'. checkP.
Qed.

(* Evaluation of functions is well sorted.                                      *)
Proposition Eval : CheckP (Function.env) Function.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Eval. checkP.
Qed.

(* Satisfaction at evaluated values is well sorted.                             *)
Proposition Satisfies : CheckP (Function.env) Function.Satisfies.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Satisfies. checkP.
Qed.

(* Range membership of evaluated values is well sorted.                         *)
Proposition IsInRange : CheckP (Function.env) Function.IsInRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.IsInRange. checkP.
Qed.

(* Class-image characterization by evaluation is well sorted.                   *)
Proposition ImageCharac : CheckP (Function.env) Function.ImageCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.ImageCharac. checkP.
Qed.

(* Set-image characterization by evaluation is well sorted.                     *)
Proposition ImageSetCharac : CheckP (Function.env) Function.ImageSetCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.ImageSetCharac. checkP.
Qed.

(* Composite domain characterization is well sorted.                            *)
Proposition DomainOfCompose : CheckP (Function.env) Function.DomainOfCompose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.DomainOfCompose. checkP.
Qed.

(* Composite evaluation for functions is well sorted.                           *)
Proposition ComposeEval : CheckP (Function.env) Function.ComposeEval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.ComposeEval. checkP.
Qed.

(* Range characterization by evaluation is well sorted.                         *)
Proposition RangeCharac : CheckP (Function.env) Function.RangeCharac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.RangeCharac. checkP.
Qed.

(* Nonempty range from nonempty domain is well sorted.                          *)
Proposition RangeIsNotEmpty : CheckP (Function.env) Function.RangeIsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.RangeIsNotEmpty. checkP.
Qed.

(* Function equality with restriction to the domain is well sorted.             *)
Proposition IsRestrict : CheckP (Function.env) Function.IsRestrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.IsRestrict. checkP.
Qed.

(* Restriction closure for functions is well sorted.                            *)
Proposition Restrict : CheckP (Function.env) Function.Restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.Restrict. checkP.
Qed.

(* Equality of restrictions from pointwise agreement is well sorted.            *)
Proposition RestrictEqual : CheckP (Function.env) Function.RestrictEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Function.RestrictEqual. checkP.
Qed.
